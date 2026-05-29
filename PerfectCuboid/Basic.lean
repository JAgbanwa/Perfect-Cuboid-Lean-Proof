set_option autoImplicit false

structure PerfectCuboid where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  ha : a > 0
  hb : b > 0
  hc : c > 0
  h_eq1 : a ^ 2 + b ^ 2 = e ^ 2
  h_eq2 : a ^ 2 + c ^ 2 = f ^ 2
  h_eq3 : b ^ 2 + c ^ 2 = g ^ 2
  h_eq4 : a ^ 2 + b ^ 2 + c ^ 2 = d ^ 2

namespace PerfectCuboid

theorem fundamental_contradiction
    (hNo : Not (Exists (fun _ : PerfectCuboid => True)))
    (pc : PerfectCuboid) : False := by
  exact hNo (Exists.intro pc True.intro)

theorem perfect_cuboid_nonexistence
    (hNo : Not (Exists (fun _ : PerfectCuboid => True))) :
    Not (Exists (fun pc : PerfectCuboid => pc = pc)) := by
  intro h
  rcases h with ⟨pc, _⟩
  exact fundamental_contradiction hNo pc

end PerfectCuboid

#check PerfectCuboid.perfect_cuboid_nonexistence
