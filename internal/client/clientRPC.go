package client

import (
	"context"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/url"
	pb "orca-peer/internal/fileshare"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
)

func RequestFileFromMarket(client pb.FileShareClient, fileDesc *pb.FileDesc) *pb.StorageIP {
	log.Printf("Requesting IP For File (%s)", fileDesc.FileName)
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	streamOfAddresses, err := client.PlaceFileRequest(ctx, fileDesc)
	if err != nil {
		log.Fatalf("client.requestFileStorage failed: %v", err)
	}
	var possible_candidates = []*pb.StorageIP{}
	for {
		storage_ip, err := streamOfAddresses.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			log.Fatalf("client.ListFeatures failed: %v", err)
		}
		log.Printf("File %s found on address: %s for the cost of %f",
			storage_ip.FileName, storage_ip.Address, storage_ip.FileCost)
		possible_candidates = append(possible_candidates, storage_ip)
		if storage_ip.IsLastCandidate {
			break
		}
	}
	var best_candidate *pb.StorageIP = nil
	for _, candidate := range possible_candidates {
		if best_candidate == nil {
			best_candidate = candidate
		} else if best_candidate.FileCost < candidate.FileCost {
			best_candidate = candidate
		}
	}
	return best_candidate
}

func RequestFileFromProducer(baseURL string, filename string) bool {
	encodedParams := url.Values{}
	encodedParams.Add("filename", filename)
	queryString := encodedParams.Encode()

	// Construct the URL with the query string
	urlWithQuery := fmt.Sprintf("%s?%s", baseURL, queryString)
	resp, err := http.Get(urlWithQuery)

	if err != nil {
		log.Fatalln(err)
	}
	//We Read the response body on the line below.
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		log.Fatalln(err)
	}
	//Convert the body to type string
	sb := string(body)
	fmt.Println(sb)
	return false
}
func DialRPC(serverAddr *string) pb.FileShareClient {
	var opts []grpc.DialOption
	opts = append(opts, grpc.WithTransportCredentials(insecure.NewCredentials()))
	conn, err := grpc.Dial(*serverAddr, opts...)
	if err != nil {
		log.Fatalf("fail to dial: %v", err)
	}
	defer conn.Close()
	client := pb.NewFileShareClient(conn)
	return client
}

func runRecordTransaction(client pb.FileShareClient, transaction *pb.FileRequestTransaction) *pb.TransactionACKResponse {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	ackResponse, err := client.RecordFileRequestTransaction(ctx, transaction)
	if err != nil {
		log.Fatalf("client.RecordFileRequestTransaction failed: %v", err)
	}
	log.Printf("ACK Response: %v", ackResponse)
	return ackResponse
}

func RecordTransactionWrapper(client pb.FileShareClient, transaction *pb.FileRequestTransaction) {
	var ack = runRecordTransaction(client, transaction)
	if ack.IsSuccess {
		fmt.Printf("[Server]: Successfully recorded transaction in hash: %v", ack.BlockHash)
	} else {
		fmt.Println("[Server]: Unable to record transaction in blockchain")
	}
}
