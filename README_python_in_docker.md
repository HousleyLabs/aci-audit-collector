# Housley ACI Audit Application - Python in Docker Method #
This script:
- Builds docker image with python libraries
- Creates container with the aci-audit-collector directory mounted as a volume
- Launches into the console of the container in the code directory


## Requirements ##
- Ensure docker and docker-compose are installed on you local PC
- Will work on Linux or Windows with WSL - not tested OSX

## Run Docker Container Script ##
```
bash rundocker.sh
```

## View Python Code Help ##
View the Python help
```
root@housley_aci_audit:/housley/code# python run.py -h
```



## Run the Audit ##
```
python run.py -a <Apic IP/Hostname> -u <User>
```
- You will be prompted for password
- Note: The password is not stored



## Close Container ##
```
root@housley_aci_audit:/housley/code# exit
```
