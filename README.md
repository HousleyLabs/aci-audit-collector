# Housley ACI Audit Application #


## Requirements ##
- Ensure docker and docker-compose are installed on you local PC
- Will work on Linux or Windows with WSL - not tested OSX


## Clone git repository ##
```
git clone https://github.com/HousleyLabs/aci-audit-collector
cd aci-audit-collector
```

You will see several folder in this audit application
- code - Python code that does the audit
- docker - Docker build files that will make a container with all appropriate libraries/packages
- output - The output files of the audit will be placed here after the audit is run


## Run Docker Container Script ##
```
bash rundocker.sh
```
This script:
- Builds docker image with python libraries
- Creates container with the aci-audit-collector directory mounted as a volume
- Launches into the console of the container in the code directory


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



## Collected Data ##
- The collected data will be placed in the output folder
- The data will also be archived into a file called output.tar.gz in the aci-audit-collector folder
- Please send the output.tar.gz to Housley for processing



## Notes ##
- If the audit process is rerun then the previously collected data and output.tar.gz will be overwritten
