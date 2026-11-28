import LeanGeodesyResearch

/-!
# Research Proof Axiom Audit

Each certified research theorem below may depend only on Lean's standard axioms.
Certificate validity checks (`*_valid`, `*_rejected`) depend only on `propext`.
Built as part of `lake build LeanGeodesyResearch`.
-/

/-- info: 'Geodesy.Spherical.kissing3Cert_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.kissing3Cert_valid

/-- info: 'Geodesy.Spherical.kissingNumber_three_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.kissingNumber_three_upper

/-- info: 'Geodesy.Spherical.kissingNumber_three_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.kissingNumber_three_lower

/-- info: 'Geodesy.Spherical.kissingNumber_three_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.kissingNumber_three_exact

/-- info: 'Geodesy.Spherical.tammes18Cert_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes18Cert_valid

/-- info: 'Geodesy.Spherical.sphericalCode_three_upper_313_500' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.sphericalCode_three_upper_313_500

/-- info: 'Geodesy.Spherical.tammes_18_strict_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes_18_strict_upper

/-- info: 'Geodesy.Spherical.arccos_313_500_lt_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.arccos_313_500_lt_deg

/-- info: 'Geodesy.Spherical.tammes_18_lt_51_25_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes_18_lt_51_25_deg

/-- info: 'Geodesy.Spherical.tammes18BV8Cert_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes18BV8Cert_valid

/-- info: 'Geodesy.Spherical.sphericalCode_three_upper_317_500' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.sphericalCode_three_upper_317_500

/-- info: 'Geodesy.Spherical.tammes_18_strict_upper_317_500' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes_18_strict_upper_317_500

/-- info: 'Geodesy.Spherical.arccos_317_500_lt_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.arccos_317_500_lt_deg

/-- info: 'Geodesy.Spherical.tammes_18_lt_50_655_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes_18_lt_50_655_deg

/-- info: 'Geodesy.Spherical.robinson18_strict_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.robinson18_strict_improvement

/-- info: 'Geodesy.Spherical.tammes18BV8BadCert_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Spherical.tammes18BV8BadCert_rejected
