# Brauer-Manin_Obstructions_on_hyperelliptic_curves
Contains magma code associated with the paper "Explicit Brauer-Manin Obstructions on Hyperelliptic Curves" by Creutz and Srivastava.

Authors: Brendan Creutz & Duttatrey Srivastava 2022
Summary: This is magma code for computing the obstruction to rational points on a hyperelliptic curve over Q coming from 2-torsion in the Brauer group.
Details of the algorithm are in the paper 'Explicit Brauer-Manin obstructions on hyperelliptic curves'

Code was developed for magma V2.25-6

BrauerSet.m contains the main intrinsic which computes the Brauer set.
BrauerSetExamples.m contains code verifying some of the claims in the paper (using the intrinsic in BrauerSet.m).
