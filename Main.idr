module Main

-- I'll add an ipkg et al later, which is better than importing everything
import Algebra.AdditiveGroups
import Algebra.BooleanRings
import Algebra.Cyclics
import Algebra.FreeGroups
import Algebra.Groups
import Algebra.Homomorphisms
import Algebra.Rings
import Algebra.Subgroups

import Categories.Definitions
import Categories.Groupoids
import Categories.Products
import Categories.UniversalProps

import Foundations.Cardinality
import Foundations.Combinatorics
import Foundations.Composition
import Foundations.DecSets
import Foundations.Equivalence
import Foundations.Functions
import Foundations.Relations
import Foundations.Sets
import Foundations.Subvectors

import NumberTheory.Church
import NumberTheory.DivisionAlgorithm
import NumberTheory.Primes

import Topology.Definitions

main : IO ()
main = putStrLn "It typechecks! Ship it!"
