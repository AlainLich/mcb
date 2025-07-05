# Notes concerning exercises

1. This directory contains a set of files used as exercises in connection with the tutorial and my attempt to port to Coq 8-20 and Hierarchy Builder(HB).
1. Porting to HB

# Remarks concerning individual files

1. exo_ch2.v: adds proofs of admitted lemmas from library
1. exo_ch4.v: same (TBD!/WIP?)
1. exo_ch5.v: provides proofs of admitted results
1. exo_ch6_bigop.v : exercise with bigop (sum of odd numbers)
1. exo_ch6_prelim.v: Exercises with direct use of Canonical (Keep?)
1. exo_ch6_seq.v: Define sequence, register it as an eqType using HB
1. exo_ch6.v: tests of chap6 material
1. exo_ch7_0.v: Redo a tuple, register with Canonical, not HB
1. exo_ch7_1.v: Redo a tuple use HB (mixin,..), hierarchical definition adding axioms gradually.
1. exo_ch7_2.v: exercises from chap 7.2, various tests
1. exo_ch7_2b.v: look at subtype_kit
1. exo_ch7_3.v: look at finite, still TBD
1. exo_ch7_4.v : look at ordinals
1. exo_ch7_5.v : finfuns, ordinals ,trees, 
1. exo_ch7plus.v: subsets, powersets, permutations, matrices
1. exo_ch8: (Only exo_ch8c.v of interest)
	- exo_ch8.v: First version, mostly done 'by hand', differs substantially concerning the representation of windrose,... limited usage of the mathcomp library. 
	- exo_ch8a.v: Cleaner version of exo_ch8b.v
	- exo_ch8b.v: Version of exo_ch8.v with additional lemmas, probing various properties.
	- exo_ch8c.v: Same as ch8.v, relies on librarie's interface to HB, only added checks and printouts.
1. exo_coercion.v: exercises with coercions
