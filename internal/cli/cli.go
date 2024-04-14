package cli

import (
	"bufio"
	"crypto/rsa"
	"fmt"
	"net"
	orcaClient "orca-peer/internal/client"
	orcaHash "orca-peer/internal/hash"
	orcaServer "orca-peer/internal/server"
	orcaStatus "orca-peer/internal/status"
	orcaStore "orca-peer/internal/store"
	"os"
	"strconv"
	"strings"
)

func StartCLI(bootstrapAddress *string, pubKey *rsa.PublicKey, privKey *rsa.PrivateKey) {
	fmt.Println("Loading...")
	ctx, dht := orcaServer.CreateDHTConnection(bootstrapAddress)
	fmt.Println("Welcome to Orcanet!")
	fmt.Println("Dive In and Explore! Type 'help' for available commands.")
	port := getPort()
	serverReady := make(chan bool)
	confirming := false
	confirmation := ""
	go orcaServer.StartServer(port, serverReady, &confirming, &confirmation)
	<-serverReady

	reader := bufio.NewReader(os.Stdin)
	client := orcaClient.NewClient("files/names/")

	for {
		fmt.Print("> ")
		text, err := reader.ReadString('\n')
		if err != nil {
			fmt.Fprintln(os.Stderr, "Error reading from stdin:", err)
			continue
		}

		text = strings.TrimSpace(text)
		parts := strings.Fields(text)
		if len(parts) == 0 {
			continue
		}

		command := parts[0]
		args := parts[1:]

		if confirming {
			switch command {
			case "yes":
				confirmation = "yes"
			default:
				confirmation = "no"
			}
			continue
		}

		switch command {
		case "get":
			if len(args) == 3 {
				go client.GetFileOnce(args[0], args[1], args[2])
			} else {
				fmt.Println("Usage: get [ip] [port] [filename]")
				fmt.Println()
			}
		case "getKey":
			if len(args) == 1 {
				go orcaServer.SearchKey(ctx, dht, args[0])
			} else {
				fmt.Println("Usage: getKey [key]")
				fmt.Println()
			}
		case "putKey":
			if len(args) == 2 {
				go orcaServer.PlaceKey(ctx, dht, args[0], args[1])
			} else {
				fmt.Println("Usage: putKey [key] [value]")
				fmt.Println()
			}
		case "fileGet":
			if len(args) == 1 {
				go func() {
					addresses := orcaServer.SearchKey(ctx, dht, args[0])
					for _, address := range addresses {
						addressParts := strings.Split(address, ":")
						if len(addressParts) == 2 {
							client.GetFileOnce(addressParts[0], addressParts[1], args[0])
						} else {
							fmt.Println("Error, got invalid address from DHT")
						}
					}
				}()
			} else {
				fmt.Println("Usage: fileGet [file hash]")
				fmt.Println()
			}
		case "fileStore":
			if len(args) == 1 {
				go func() {
					fileHash, err := orcaHash.HashFile(args[0])
					if err != nil {
						fmt.Println(err)
						return
					}
					fileHashStr := string(fileHash)
					address := "localhost" + ":" + port
					orcaServer.PlaceKey(ctx, dht, fileHashStr, address)
				}()
			} else {
				fmt.Println("Usage: fileStore [file path]")
				fmt.Println()
			}
		case "store":
			if len(args) == 3 {
				go client.RequestStorage(args[0], args[1], args[2])
			} else {
				fmt.Println("Usage: store [ip] [port] [filename]")
				fmt.Println()
			}
		case "import":
			if len(args) == 1 {
				go client.ImportFile(args[0])
			} else {
				fmt.Println("Usage: import [filepath]")
				fmt.Println()
			}
		case "location":
			fmt.Println(orcaStatus.GetLocationData())
		case "network":
			fmt.Println("Testing Network Speeds...")
			networkData := orcaStatus.GetNetworkInfo()
			if networkData.Success {
				fmt.Printf("Latency: %fms, Download: %fMbps, Upload: %fMbps\n", networkData.LatencyMs, networkData.DownloadSpeedMbps, networkData.UploadSpeedMbps)
			} else {
				fmt.Println("Unable to test network speeds. Please try again")
			}

		case "list":
			files := orcaStore.GetAllLocalFiles()
			fmt.Print("Files found:")
			for _, file := range files {
				fmt.Println(file.Name)
			}
		case "hash":
			if len(args) == 1 {
				orcaHash.HashFile(args[0])
			} else {
				fmt.Println("Usage: hash [fileName]")
				fmt.Println()
			}
		case "send":
			if len(args) == 3 {
				cost, err := strconv.ParseFloat(args[0], 64)
				if err != nil {
					fmt.Println("Error parsing amount to send")
					continue
				}
				orcaClient.SendTransaction(cost, args[1], args[2], pubKey, privKey)
			} else {
				fmt.Println("Usage: send [amount] [ip] [port]")
				fmt.Println()
			}

		case "exit":
			fmt.Println("Exiting...")
			return
		case "getdir":
			if len(args) == 3 {
				go client.GetDirectory(args[0], args[1], args[2])
			} else {
				fmt.Println("Usage: getdir [ip] [port] [path]")
				fmt.Println()
			}
		case "storedir":
			if len(args) == 3 {
				go client.StoreDirectory(args[0], args[1], args[2])
			} else {
				fmt.Println("Usage: storedir [ip] [port] [path]")
				fmt.Println()
			}
		case "help":
			fmt.Println("COMMANDS:")
			fmt.Println(" get [ip] [port] [filename]     Request a file")
			fmt.Println(" store [ip] [port] [filename]   Request storage of a file")
			fmt.Println(" getdir [ip] [port] [path]     Request a directory")
			fmt.Println(" storedir [ip] [port] [path]   Request storage of a directory")
			fmt.Println(" putKey [key] [value]           Put a key in the DHT")
			fmt.Println(" getKey [key]                   Retreieve key from DHT")
			fmt.Println(" import [filepath]              Import a file")
			fmt.Println(" fileGet [fileHash]            Get the file from the network")
			fmt.Println(" send [amount] [ip] [amount]    Send an amount of money to network")
			fmt.Println(" hash [fileName]                Get the hash of a file")
			fmt.Println(" list                           List all files you are storing")
			fmt.Println(" location                       Print your location")
			fmt.Println(" network                        Test speed of network")
			fmt.Println(" exit                           Exit the program")
			fmt.Print()
		default:
			fmt.Println("Unknown command. Type 'help' for available commands.")
			fmt.Println()
		}
	}
}

// Ask user to enter a port and returns it
func getPort() string {
	reader := bufio.NewReader(os.Stdin)

	fmt.Print("Enter a port number to start listening to requests: ")
	for {
		port, err := reader.ReadString('\n')
		if err != nil {
			fmt.Println("Error reading input:", err)
			os.Exit(1)
		}
		port = strings.TrimSpace(port)

		// Validate port
		listener, err := net.Listen("tcp", ":"+port)
		if err == nil {
			defer listener.Close()
			return port
		}

		fmt.Print("Invalid port. Please enter a different port: ")
	}
}
