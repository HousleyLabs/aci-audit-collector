# Housley ACI Audit Application #



## Clone git repository ##
- Change to a folder where the application will be installed
- The git cloning process will create a subfolder called aci-audit-collector

```
git clone https://github.com/HousleyLabs/aci-audit-collector
cd aci-audit-collector
```

### Content of Git Repository ###
You will see inside the newly created folder several subfolders
- code - Python code that does the audit for the docker method
- curl - Contains code using curl method
- docker - Docker build files that will make a container with all appropriate libraries/packages
- output - The output files of the audit will be placed here after the audit is run


## Choose a Method to run the ACI Audit ##
- [Python in Docker Method](README_python_in_docker.md)
- [Curl in Bash Method](README_curl_in_bash.md)



## Collected Data ##
- The collected data will be placed in the output folder
- The data will also be archived into a file called output.tar.gz in the aci-audit-collector folder
- Please send the output.tar.gz to Housley for processing



## Notes ##
- If the audit process is rerun then the previously collected data and output.tar.gz will be overwritten
