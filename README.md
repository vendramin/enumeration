# enumerations 

The repository contains database of several finite non-associative structures. This is based on the preprint 

> Ö. Akgün, M. Mereb, L. Vendramin. Enumeration of set-theoretic solutions to the Yang-Baxter equation. _Math. Comp. 91 (2022), 1469-1481_. Preprint: [arXiv:2008.04483](https://arxiv.org/abs/2008.04483).

Here is a short description of some of the files. 

## IYB: Involutive solutions to the YBE 

There are several ways to approach the construction of solutions:
* `parserA.g`. The method here is to send as constraint all permutations in the centralizer of T whenever the centralizer is small enough, and a generating set of this centralizer otherwise. 
* `parserB.g`. The method here consists of sending as constaints all permutations in the centralizer of T whenever the centalizer is small enough, and those permutations of the centralizer that move at most 3 points otherweise.       
* `parserC.g`. The method here is to send as constraints all products of at most 3 elements of a generating set of the centralizer of T. 

These files were used to construct involutive solutions (up to isomorphism) of size at most 10.  
You will find the database (for GAP) in `data` and logfiles corresponding to the different methods in `logs`. 

To construct solutions of size nine, one loads the file needed, for example `gap parserC.g` and then run the following command:

`gap> construct(9);`

## YB: Non-involutive solutions

Solutions of size eight are [here](https://vub-my.sharepoint.com/:u:/g/personal/leandro_vendramin_vub_be/ESfStwqaoURGpQvbRSjrb2EBv5OErY-5dI6H3ILX62nVHQ?e=mD0y3a)
