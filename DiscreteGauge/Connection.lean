import Mathlib

/-!
# Discrete gauge theory on a quiver

A lattice gauge field: a group element on every edge (parallel transport), acted on by
gauge transformations at the vertices. The main results say that holonomy is
gauge-covariant, so Wilson loops and flatness are gauge-invariant.
-/

namespace DiscreteGauge

/-- A connection assigns a group element to every edge. 

@dataclass(frozen=True)
class Connection(Generic[V, G]):
    U: Callable[[Edge[V]], G]
-/
@[ext]
structure Connection (V : Type*) [Quiver V] (G : Type*) where
  U : ∀ {a b : V}, (a ⟶ b) → G

section Quiver

/- Define for this section that V is a quiver, G A
group
-/
variable {V : Type*} [Quiver V] {G : Type*} [Group G]

/-- The gauge transformation `g : V → G` acts by `U e ↦ g a * U e * (g b)⁻¹`. 

def gauge(g: Callable[[V], G], A: Connection) -> Connection:
    return Connection(U=lambda e: g(e.src) * A.U(e) * g(e.dst).inverse())
-/
def gauge (g : V → G) (A : Connection V G) : Connection V G where
  U {a b} e := g a * A.U e * (g b)⁻¹

/-- The set of gauge transformations has an identity. -/
theorem gauge_one (A : Connection V G) : gauge 1 A = A := by
  sorry

/-- Gauge transformations multiply as group actions. 

LHS: Pointwise product
RHS: Composite product 
-/
theorem gauge_mul (g h : V → G) (A : Connection V G) :
    gauge (g * h) A = gauge g (gauge h A) := by
  sorry

/-- Parallel transport along a path. 

# list[Edge] is weaker than Quiver.Path (which is connected)
def hol(A: Connection, path: list[Edge]) -> G:
    if not path:
        return identity
    *p, e = path
    return hol(A, p) * A.U(e)
-/
def hol (A : Connection V G) : ∀ {a b : V}, Quiver.Path a b → G
  | _, _, .nil => 1
  | _, _, .cons p e => hol A p * A.U e

/-- Holonomy is multiplicative -/
theorem hol_comp (A : Connection V G) {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    hol A (p.comp q) = hol A p * hol A q := by
  sorry

/-- Holonomy is gauge-covariant. -/
theorem hol_gauge (g : V → G) (A : Connection V G) {a b : V} (p : Quiver.Path a b) :
    hol (gauge g A) p = g a * hol A p * (g b)⁻¹ := by
  sorry

/-- Around a loop, holonomy changes by conjugation. -/
theorem hol_gauge_loop (g : V → G) (A : Connection V G) {a : V} (p : Quiver.Path a a) :
    hol (gauge g A) p = g a * hol A p * (g a)⁻¹ :=
  hol_gauge g A p

/-- Any class function of the holonomy (e.g. a trace) is gauge-invariant. -/
theorem wilson_invariant {R : Type*} (f : G → R) (hf : ∀ h x, f (h * x * h⁻¹) = f x)
    (g : V → G) (A : Connection V G) {a : V} (p : Quiver.Path a a) :
    f (hol (gauge g A) p) = f (hol A p) := by
  sorry

end Quiver

/-- A lattice: a quiver together with its plaquettes (the elementary closed loops). 

These correspond to infinitesimal loops, and are necessary to define curvature.
They are sometimes naturally defined via 2-cells.
-/
class GaugeLattice (V : Type*) extends Quiver V where
  plaquettes : Set (Σ a : V, Quiver.Path a a)

section GaugeLattice

variable {V : Type*} [GaugeLattice V] {G : Type*} [Group G]

/-- `A` is flat if every plaquette of the lattice has trivial holonomy. 

def flat(lattice: GaugeLattice, A: Connection) -> bool:
    return all(hol(A, loop) == identity for (_, loop) in lattice.plaquettes)
-/
def Flat (A : Connection V G) : Prop :=
  ∀ plaq ∈ GaugeLattice.plaquettes (V := V), hol A plaq.2 = 1

/-- Gauge transformations preserve flatness. -/
theorem flat_gauge (g : V → G) (A : Connection V G) (hA : Flat A) : Flat (gauge g A) := by
  sorry

end GaugeLattice

end DiscreteGauge
