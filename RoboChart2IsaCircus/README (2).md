# RoboChart to IsaCircus Transformation

## This project contains the implementation of the transformation from RoboChart to IsaCircus. It has two steps:
RoboChart to Circus by model-to-model transformation
Circus to IsaCircus by model-to-text transformation

## Environment setup
### Installation of Epsilon 2.4 through Eclipse installer
### Then, the RoboChart notation will be installed using the updated website: https://robostar.cs.york.ac.uk/robotool/update/. Note: only to install the RoboChart package
### Import the project, and register the Circus Metamodel by right-clicking "circus_metamodel.ecore" file and selecting "register EPackage"

## Run test
### Step 1: go to folder "test1", right-click the launch file "RC2Circus_test1.launch", then "Run As", then the Circus model "test1_circus.model" is generated from the RoboChart model "test1.model". Note: As the RoboChart model "test1.model" will be changed each time the transformation is run, so this model needs to be kept in a separate folder, and used to replace the file "test1.model" in the folder "test1",
### Step 2: go to folder "test1", right-click the launch file "Circus2IsaCircus_test1.launch", then "Run As", then the IsaCircus model can be generated as a theory file.
