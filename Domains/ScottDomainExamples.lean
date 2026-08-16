/- ================================================================
   Scott domain examples — the catalogue, as a module map.

   This file is now an aggregator: importing it brings in every part.
   The mathematics is catalogued in ../docs/ScottDomainExamples.md and
   split across modules so that no single file has to be read whole.

     Enumeration      lists of bounded length, shared machinery
     Finite           §3.1 𝟙 · §3.2/§4 𝕊 · §3.3 𝔹⊥ · §3.4 ω+1 · §3.5 finite bd-compl.
     Infinite         §3.6 𝒫(ℕ) · §3.7 ℕ⇀ℕ · §3.8 streams
                      — also `psetBits` and `pairDecode`, the bit-mask and
                        pairing machinery later sections enumerate with
     IdealCompletion  §5.6 Idl(P), the general theorem the rest of §5 rests on
     FunctionSpace    §5.1 [D→E], and its bijection with the continuous maps
     LambdaModels     §5.2 parallel-or · §5.3 Pω as a λ-model
     TermDomains      §5.4 T^∞(Σ)
     DInfinity        §5.5 the tower, the flat encoding, and the bilimit
     NonExamples      §6.1 two minimal upper bounds · §6.2 ℕ not a dcpo ·
                      §6.5 powerdomains

   Not here, and deliberately so:

   - §6.3 and §6.4 need ℝ, hence Mathlib, and live in `IntervalDomain.lean`.
     Every module above imports nothing outside this repository, which is
     what keeps layer S's restrictions from being bypassed through Lean's
     ambient library — and what keeps `Classical.choice` out of all of them.
   - §3.2's witness `sierp` is in `LRSODInCIC.lean` itself; `Finite` adds
     the proof that its three opens are all of them.

   Module order follows dependency, which for §5 also happens to be the
   mathematical order: §5.6 is the general theorem and §5.1, §5.4, §5.5
   and §6.5 are instances of it, so it precedes them.
   ================================================================ -/

import Domains.LRSODInCIC
import Domains.Enumeration
import Domains.Finite
import Domains.Infinite
import Domains.IdealCompletion
import Domains.FunctionSpace
import Domains.LambdaModels
import Domains.TermDomains
import Domains.DInfinity
import Domains.NonExamples
