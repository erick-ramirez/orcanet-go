package server

import (
	"bufio"
	"context"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/pem"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"net/http"
	"orca-peer/internal/fileshare"
	"os"
	"regexp"
	"strings"
	"sync"
	"time"

	"github.com/libp2p/go-libp2p"
	dht "github.com/libp2p/go-libp2p-kad-dht"
	record "github.com/libp2p/go-libp2p-record"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/peer"
	drouting "github.com/libp2p/go-libp2p/p2p/discovery/routing"
	dutil "github.com/libp2p/go-libp2p/p2p/discovery/util"
	"github.com/multiformats/go-multiaddr"
	"google.golang.org/protobuf/proto"
)

type OrcaValidator struct{}

func (v OrcaValidator) Validate(key string, value []byte) error {
	// verify key is a sha256 hash
	hexPattern := "^[a-fA-F0-9]{64}$"
	regex := regexp.MustCompile(hexPattern)
	if !regex.MatchString(strings.Replace(key, "orcanet/market/", "", -1)) {
		return errors.New("provided key is not in the form of a SHA-256 digest")
	}

	pubKeySet := make(map[string]bool)

	for i := 0; i < len(value)-8; i++ {
		messageLength := uint16(value[i+1])<<8 | uint16(value[i])
		digitalSignatureLength := uint16(value[i+3])<<8 | uint16(value[i+2])
		contentLength := messageLength + digitalSignatureLength
		user := &fileshare.User{}

		err := proto.Unmarshal(value[i+4:i+4+int(messageLength)], user)
		if err != nil {
			return err
		}

		if pubKeySet[string(user.GetId())] {
			return errors.New("duplicate record for the same public key found")
		} else {
			pubKeySet[string(user.GetId())] = true
		}

		userMessageBytes := value[i+4 : i+4+int(messageLength)]

		publicKey, err := crypto.UnmarshalRsaPublicKey(user.GetId())
		if err != nil {
			return err
		}

		signatureBytes := value[i+4+int(messageLength) : i+4+int(contentLength)]
		valid, err := publicKey.Verify(userMessageBytes, signatureBytes) //this function will automatically compute hash of data to compare signauture

		if err != nil {
			return err
		}

		if !valid {
			return errors.New("signature invalid")
		}

		i = i + 4 + int(contentLength) - 1
	}

	currentTime := time.Now().UTC()
	unixTimestamp := currentTime.Unix()
	unixTimestampInt64 := uint64(unixTimestamp)

	suppliedTime := ConvertBytesTo64BitInt(value[len(value)-8:])
	if suppliedTime > unixTimestampInt64 {
		return errors.New("supplied time cannot be less than current time")
	}
	return nil
}

func (v OrcaValidator) Select(key string, value [][]byte) (int, error) {
	max := len(value[0])
	maxIndex := 0
	latestTime := ConvertBytesTo64BitInt(value[0][(len(value[0]) - 8):])
	for i := 1; i < len(value); i++ {
		suppliedTime := ConvertBytesTo64BitInt(value[i][(len(value[i]) - 8):])
		fmt.Println(suppliedTime)
		if len(value[i]) >= max {
			if suppliedTime >= latestTime {
				max = len(value[i])
				latestTime = suppliedTime
				maxIndex = i
			}
		}
	}
	return maxIndex, nil
}

type fileShareServerNode struct {
	fileshare.UnimplementedFileShareServer
	savedFiles   map[string][]*fileshare.FileDesc // read-only after initialized
	mu           sync.Mutex                       // protects routeNotes
	currentCoins float64
}

func CreateDHTConnection(bootstrapAddress *string) (context.Context, *dht.IpfsDHT) {
	if *bootstrapAddress == "local" {
		return nil, nil
	}

	// "/ip4/194.113.75.165/tcp/44981/p2p/QmS6bES2qGSCN1vTmxEjZGDwwLw5Lsm2ToAcpzf97S7BnR"
	ctx := context.Background()

	//Generate private key for peer``
	privKey, _, err := crypto.GenerateKeyPair(crypto.RSA, 2048)
	if err != nil {
		panic(err)
	}

	//Construct multiaddr from string and create host to listen on it
	sourceMultiAddr, _ := multiaddr.NewMultiaddr("/ip4/0.0.0.0/tcp/44981")
	opts := []libp2p.Option{
		libp2p.ListenAddrStrings(sourceMultiAddr.String()),
		libp2p.Identity(privKey), //derive id from private key
	}
	host, err := libp2p.New(opts...)
	if err != nil {
		panic(err)
	}

	log.Printf("Host ID: %s", host.ID())
	log.Printf("Connect to me on:")
	for _, addr := range host.Addrs() {
		log.Printf("%s/p2p/%s", addr, host.ID())
	}

	//An array if we want to expand to a more stable peer list instead of providing in args
	bootstrapPeers := ReadBootstrapPeers()

	// Start a DHT, for use in peer discovery. We can't just make a new DHT
	// client because we want each peer to maintain its own local copy of the
	// DHT, so that the bootstrapping node of the DHT can go down without
	// inhibiting future peer discovery.
	var validator record.Validator = OrcaValidator{}
	var options []dht.Option

	// Start a DHT in client mode for now, until we can detect if we are
	// behind a NAT
	options = append(options, dht.Mode(dht.ModeClient))
	options = append(options, dht.ProtocolPrefix("orcanet/market"), dht.Validator(validator))
	kDHT, err := dht.New(ctx, host, options...)
	if err != nil {
		panic(err)
	}

	// Bootstrap the DHT. In the default configuration, this spawns a Background
	// thread that will refresh the peer table every five minutes.
	log.Println("Bootstrapping the DHT")
	if err = kDHT.Bootstrap(ctx); err != nil {
		panic(err)
	}

	// Let's connect to the bootstrap nodes first. They will tell us about the
	// other nodes in the network.
	var wg sync.WaitGroup
	for _, peerAddr := range bootstrapPeers {
		peerinfo, _ := peer.AddrInfoFromP2pAddr(peerAddr)
		wg.Add(1)
		go func() {
			defer wg.Done()
			if err := host.Connect(ctx, *peerinfo); err != nil {
				log.Println("WARNING: ", err)
			} else {
				log.Println("Connection established with bootstrap node:", *peerinfo)
			}
		}()
	}
	wg.Wait()

	go discoverPeers(ctx, host, kDHT, "orcanet/market")

	return ctx, kDHT
}

func PlaceKey(ctx context.Context, kDHT *dht.IpfsDHT, putKey string, putValue string) {
	err := kDHT.PutValue(ctx, "orcanet/market/"+putKey, []byte(putValue))
	if err != nil {
		fmt.Println("Error: ", err)
		time.Sleep(5 * time.Second)
		return
	}
	fmt.Println("Put key: ", putKey+" Value: "+putValue)
	fmt.Print("> ")
}
func SearchKey(ctx context.Context, kDHT *dht.IpfsDHT, searchKey string) []string {
	valueStream, err := kDHT.SearchValue(ctx, "orcanet/market/"+searchKey)
	fmt.Println("Searching for " + searchKey)
	fmt.Print("> ")
	if err != nil {
		fmt.Println("Error: ", err)
		time.Sleep(5 * time.Second)
		return nil
	}
	time.Sleep(5 * time.Second)
	allAddress := make([]string, 0)
	for byteArray := range valueStream {
		allAddress = append(allAddress, string(byteArray))
		fmt.Print("Found value: ")
		fmt.Println(string(byteArray))
		fmt.Print("> ")
	}
	return allAddress
}
func discoverPeers(ctx context.Context, h host.Host, kDHT *dht.IpfsDHT, advertise string) {
	routingDiscovery := drouting.NewRoutingDiscovery(kDHT)
	if kDHT.Mode() == dht.ModeServer {
		dutil.Advertise(ctx, routingDiscovery, advertise)
	}
	// Look for others who have announced and attempt to connect to them
	for {
		//fmt.Println("Searching for peers...")
		peerChan, err := routingDiscovery.FindPeers(ctx, advertise)
		if err != nil {
			panic(err)
		}
		for peer := range peerChan {
			if peer.ID == h.ID() {
				continue // No self connection
			}
			err := h.Connect(ctx, peer)
			if err != nil {
				fmt.Printf("Failed connecting to %s, error: %s\n", peer.ID, err)
			} else {
				// fmt.Println("Connected to:", peer.ID)
			}
		}
		time.Sleep(time.Second * 10)
	}
}

func sendFileToConsumer(w http.ResponseWriter, r *http.Request) {
	switch r.Method {
	case "GET":
		for k, v := range r.URL.Query() {
			fmt.Printf("%s: %s\n", k, v)
		}
		// file = r.URL.Query().Get("filename")
		w.Write([]byte("Received a GET request\n"))

	default:
		w.WriteHeader(http.StatusNotImplemented)
		w.Write([]byte(http.StatusText(http.StatusNotImplemented)))
	}
	w.Write([]byte("Received a GET request\n"))
	filename := r.URL.Path[len("/reqFile/"):]

	// Open the file
	file, err := os.Open(filename)
	if err != nil {
		http.Error(w, err.Error(), http.StatusNotFound)
		return
	}
	defer file.Close()

	// Set content type
	contentType := "application/octet-stream"
	switch {
	case filename[len(filename)-4:] == ".txt":
		contentType = "text/plain"
	case filename[len(filename)-5:] == ".json":
		contentType = "application/json"
		// Add more cases for other file types if needed
	}

	// Set content disposition header
	w.Header().Set("Content-Disposition", "attachment; filename="+filename)
	w.Header().Set("Content-Type", contentType)

	// Copy file contents to response body
	_, err = io.Copy(w, file)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
}

func runNotifyStore(client fileshare.FileShareClient, file *fileshare.FileDesc) *fileshare.StorageACKResponse {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	ackResponse, err := client.NotifyFileStore(ctx, file)
	if err != nil {
		log.Fatalf("client.NotifyFileStorage failed: %v", err)
	}
	log.Printf("ACK Response: %v", ackResponse)
	return ackResponse
}

func runNotifyUnstore(client fileshare.FileShareClient, file *fileshare.FileDesc) *fileshare.StorageACKResponse {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	ackResponse, err := client.NotifyFileUnstore(ctx, file)
	if err != nil {
		log.Fatalf("client.NotifyFileStorage failed: %v", err)
	}
	log.Printf("ACK Response: %v", ackResponse)
	return ackResponse
}

func NotifyStoreWrapper(client fileshare.FileShareClient, file_name_hash string, file_name string, file_size_bytes int64, file_origin_address string, origin_user_id string, file_cost float32, file_data_hash string, file_bytes []byte) {
	var file_description = fileshare.FileDesc{FileNameHash: file_name_hash,
		FileName:          file_name,
		FileSizeBytes:     file_size_bytes,
		FileOriginAddress: file_origin_address,
		OriginUserId:      origin_user_id,
		FileCost:          file_cost,
		FileDataHash:      file_data_hash,
		FileBytes:         file_bytes}
	var ack = runNotifyUnstore(client, &file_description)
	if ack.IsAcknowledged {
		fmt.Printf("[Server]: Market acknowledged stopping storage of file %s with hash %s \n", ack.FileName, ack.FileHash)
	} else {
		fmt.Printf("[Server]: Unable to notify market that we are stopping the storage of file %s with hash %s \n", ack.FileName, ack.FileHash)
	}
}
func NotifyUnstoreWrapper(client fileshare.FileShareClient, file_name_hash string, file_name string, file_size_bytes int64, file_origin_address string, origin_user_id string, file_cost float32, file_data_hash string, file_bytes []byte) {
	var file_description = fileshare.FileDesc{FileNameHash: file_name_hash,
		FileName:          file_name,
		FileSizeBytes:     file_size_bytes,
		FileOriginAddress: file_origin_address,
		OriginUserId:      origin_user_id,
		FileCost:          file_cost,
		FileDataHash:      file_data_hash,
		FileBytes:         file_bytes}
	var ack = runNotifyUnstore(client, &file_description)
	if ack.IsAcknowledged {
		fmt.Printf("[Server]: Market acknowledged stopping storage of file %s with hash %s \n", ack.FileName, ack.FileHash)
	} else {
		fmt.Printf("[Server]: Unable to notify market that we are stopping the storage of file %s with hash %s \n", ack.FileName, ack.FileHash)
	}
}

// Function needs to be changed since it looks for privateKey.pem ?
func CheckOrCreatePrivateKey(path string) (crypto.PrivKey, error) {
	// Check if the privateKey.pem exists
	_, err := os.Stat(path)
	if os.IsNotExist(err) {
		// No private key file, so let's create one
		privKey, err := rsa.GenerateKey(rand.Reader, 2048)
		if err != nil {
			return nil, err
		}
		privKeyBytes := x509.MarshalPKCS1PrivateKey(privKey)
		privKeyPEM := pem.EncodeToMemory(&pem.Block{
			Type:  "RSA PRIVATE KEY",
			Bytes: privKeyBytes,
		})
		err = ioutil.WriteFile(path, privKeyPEM, 0600)
		if err != nil {
			return nil, err
		}
		log.Println("New private key generated and saved to", path)

		libp2pPrivKey, _, err := crypto.KeyPairFromStdKey(privKey)
		if err != nil {
			return nil, err
		}

		return libp2pPrivKey, nil
	} else if err != nil {
		// Some other error occurred when trying to read the file
		return nil, err
	}

	// Private key file exists, let's read it
	privKeyBytes, err := ioutil.ReadFile(path)
	if err != nil {
		return nil, err
	}
	block, _ := pem.Decode(privKeyBytes)
	if block == nil || block.Type != "RSA PRIVATE KEY" {
		log.Println("Private key file is of invalid format")
		return nil, errors.New("private key file is of invalid format")
	}
	privKey, err := x509.ParsePKCS1PrivateKey(block.Bytes)
	if err != nil {
		return nil, err
	}
	log.Println("Existing private key loaded from", path)

	libp2pPrivKey, _, err := crypto.KeyPairFromStdKey(privKey)
	if err != nil {
		return nil, err
	}

	return libp2pPrivKey, nil
}

// Find file bootstrap.peers and parse it to get multiaddrs of bootstrap peers
func ReadBootstrapPeers() []multiaddr.Multiaddr {
	peers := []multiaddr.Multiaddr{}

	// For now bootstrap.peers can be in cli folder but it can be moved
	file, err := os.Open("internal/cli/bootstrap.peers")
	if err != nil {
		panic(err)
	}

	scanner := bufio.NewScanner(file)
	scanner.Split(bufio.ScanLines)

	for scanner.Scan() {
		line := scanner.Text()

		multiadd, err := multiaddr.NewMultiaddr(line)
		if err != nil {
			panic(err)
		}
		peers = append(peers, multiadd)
	}

	return peers
}

func ConvertBytesTo64BitInt(value []byte) uint64 {
	suppliedTime := uint64(0)
	shift := 7
	for i := 0; i < len(value); i++ {
		suppliedTime = suppliedTime | (uint64(value[i]) << (shift * 8))
		shift--
	}
	return suppliedTime
}
