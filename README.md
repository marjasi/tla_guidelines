# TLA+ specification writing guidelines
This repository contains files relevant to my master's thesis on TLA+ specification writing guidelines for state space reduction.

# Files
- `Guidelines.drawio` - definitions of guidelines and their application detection algorithm.
- `NodeActionsParse.py` - partial implementation of the guideline detection algorithm for the node actions guideline.
- `StateSpaceChange.csv`- state space size data collected by running TLC on created TLA+ specifications.
- The `Specifications` folder contains all TLA+ specifications and configuration files presented as results of the thesis.
- TLC model checking `.out` files that show that safety and liveness properties were verified are located in the `TLCOutput` folder.