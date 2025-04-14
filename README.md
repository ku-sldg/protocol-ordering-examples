# Attestation Protocol Ordering Examples

Example attestation protocol analyses using the AttestationProtocolOrdering 
Coq library. Orders attestation protocols by their difficulty to attack.

## Meta

- Author(s):
  - Sarah Johnson
  - Anna Fritz
  - Perry Alexander
- Compatible Coq versions: 8.20 or later
- Additional dependencies: `AttestationProtocolOrdering`

## Building and installation instructions

### Prerequisites
Clone the AttestationProtocolOrdering repository at
git@github.com:ku-sldg/protocol-ordering.git
and follow the build instructions in the README.md to install 
a local version of the library.


Download the Copland Collection at
https://ku-sldg.github.io/copland/resources/copland-collection.tgz
and follow the installation instructions in the README.md to install
Chase and the Copland theory.

### Provided Examples
Generate and compile the provided examples with:
```
(cd scripts/ ; bash setup.sh <foldername>)
make
```
Option for `<foldername>` is *examples0* and *examples1*. 

The Chase output in XHTML can be found in the `<foldername>/chase-outputs` 
directory. The attack graphs in Coq can be found in the `<foldername>` directory.

### User-Defined Examples
Copy the `template` directory and give it a name of your choosing. 
```
cp -r template/ <foldername>
```

Add pairs of files with names in the form `<basename>.cop` and `<basename>.gln` 
to the `chase-inputs` directory containing a Copland protocol and its corresponding 
system assumptions respectively. 

Complete the `components.v` file by defining a type that represents the set of 
system components appearing in your protocols and completing a proof that this 
type has decidable equality. 

Generate and compile your example with:
```
(cd scripts/ ; bash setup.sh <foldername>)
make
```

To analyze and order your protocols, create a Coq file. Import the AttestationProtocolOrdering 
library and the generated attack graphs with:
```
Require Import AttestationProtocolOrdering.<libname>.
Require Import ProtocolOrderingExamples.<basename>.
```
Options for `<libname>` are *attackgraph*, *attackgraph_normalization*, *attackgraph_ordering*,
*set_minimization*, *set_ordering*, and *set_relationship*.




## Documentation

### Scripts
All scripts are unverified and contain only crude error handling. They are intended only
as a convenience.

`xhtml2coq.py`: Python script to convert Chase output in XHMTL to attack graphs in Coq.

`getAttacks.sh`: Bash script to find and convert attacks of a specified protocol.

`getAllAttacks.sh`: Bash script to find and convert attacks of all protocols.

`genCoqProject.py`: Python script to generate a _CoqProject file for a given foldername.

`setup.sh`: Bash script to get all attacks and generate _CoqProject.
