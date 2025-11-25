# Verification with Batfish
This directory contains some documentation and instructions for running the verification tool for networks that we are developing using Batfish. Additionally, there a few examples documenting the current state of the tool.

## Getting Started
1. Clone the verification branch of the repo... if you are reading this README, then you are looking at the correct branch. The url for the correct branch is linked [here](https://github.com/ana-brendel/batfish/tree/verification#).
2. Follow these instructions to download support for building with Bazel. _**TODO** get link_
3. You should create a virtual python environment. You will have to install any dependencies including `pybatfish`. The `pybatfish` instructions might be helpful if you get stuff; they're located [here](https://github.com/batfish/pybatfish/blob/master/README.md). To do this and install dependencies, run the following commands:
```
directory % cd .../batfish/verification
directory/batfish/verification % virtualenv -p python3 .
directory/batfish/verification % source ./bin/activate
directory/batfish/verification % pip install pandas 
directory/batfish/verification % pip install jinja2 
directory/batfish/verification % python3 -m pip install --upgrade pip
directory/batfish/verification % python3 -m pip install --upgrade pybatfish
```

## Running Batfish on Examples
_**To run Batfish, execute the following commands:**_
```
directory % cd .../batfish
directory/batfish % ./tools/bazel_run.sh
```
This command will not terminate, but it will start the Batfish process so that the `pybatfish` client can query. It should tell you `Build completed successfully` and then continue running the program in the page waiting for the `pybatfish` client to query.


_**To run the provided examples, look at the jupyter notebook in this directory titled (VerificationExamples.ipynb).**_