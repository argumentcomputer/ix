import IxCC.Recheck.Rc.Proof.KeyIndex

/-! Exact axiom inventory of RC policy selection's linear form: the key index gives
`funList.find?`'s answer, the one-pass merges are the indexed ones, and `enrichFirContracts`
(hence `selectRcPolicyForSrc`) is its former list form. `Classical.choice` enters through the
standard library's lemma on a hash map's insertion (`Std.HashMap.getElem?_insert`). -/

/-- info: 'IxCC.Own.Plain.mergeContracts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.mergeContracts_eq

/-- info: 'IxCC.Own.Plain.keepContracts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.keepContracts_eq

/-- info: 'IxCC.Own.Plain.keyIndex_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.keyIndex_getElem?

/-- info: 'IxCC.Own.Plain.progKeyContractsBy_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.progKeyContractsBy_eq

/-- info: 'IxCC.Own.Plain.progKeyResultBy_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.progKeyResultBy_eq

/-- info: 'IxCC.Own.Plain.enrichFirContracts_eq_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.enrichFirContracts_eq_list

/-- info: 'IxCC.Own.Plain.selectRcPolicyForSrc_eq_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.selectRcPolicyForSrc_eq_list
