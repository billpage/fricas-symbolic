-- The axioms each cited theorem rests on (skill `lean`, "Recorded results").
-- Run with run_lean(project="fricas-symbolic") after a lean_build of the cited commit.
-- Each line must list at most propext, Classical.choice and Quot.sound.
import FricasSymbolic

#print axioms FricasSymbolic.sAdd_refines
#print axioms FricasSymbolic.sSub_refines
#print axioms FricasSymbolic.sNeg_refines
#print axioms FricasSymbolic.sMul_refines
#print axioms FricasSymbolic.sDiv_refines
#print axioms FricasSymbolic.sPow_refines
#print axioms FricasSymbolic.nf_refines
#print axioms FricasSymbolic.L7_without_AN
#print axioms FricasSymbolic.L7_with_AN
#print axioms FricasSymbolic.L10_id_without_num
#print axioms FricasSymbolic.L10_not_confluent
#print axioms FricasSymbolic.L9_terminating
#print axioms FricasSymbolic.L4_nf_isNF
#print axioms FricasSymbolic.L6_nf_of_isNF
#print axioms FricasSymbolic.nf_nf
#print axioms FricasSymbolic.L8_steps_to_nf
#print axioms FricasSymbolic.sAdd_assoc
#print axioms FricasSymbolic.sMul_assoc
#print axioms FricasSymbolic.L5_step
#print axioms FricasSymbolic.L5_eqA
#print axioms FricasSymbolic.eqA_iff_nf_eq
#print axioms FricasSymbolic.church_rosser
#print axioms FricasSymbolic.unique_nf
