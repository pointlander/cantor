# A theory of everything from two infinities

At the origin of time, quantum field theory and general relativity are
one theory, and that theory has the infinity of the countable numbers.
After time passes they separate: QFT keeps the countable infinity, while
GR is carried by the infinity of the reals. The split is sharp — Cantor’s
diagonal argument proves the two infinities are not the same, so the
theories cannot be identified once the continuum has appeared.

This repository is a Lean 4 formalization of that claim.

## The claim

A physical theory is a kinematic carrier together with the infinity that
carrier bears.

| Epoch | Contents | Infinity |
|---|---|---|
| Origin (`t = 0`) | one unified theory | countable numbers `ℕ` |
| After time (`t > 0`) | QFT | countable numbers `ℕ` |
| After time (`t > 0`) | GR | the reals (`ℕ → Bool`, equinumerous with `ℝ`) |

QFT after the split **is** the original countable carrier: a separable
Fock space, modes labelled by `ℕ`. GR after the split is the **power
object** of that carrier — the space of maps `Carrier → Bool`. Gravity
is not another copy of the quantum modes. It is the continuum of
predicates on those modes, which is why spacetime looks like `ℝ⁴` and
why `|ℝ⁴| = |ℝ|`.

Cosmic time is indexed by `ℕ`. Time zero is the origin. Every later
instant is after the split. We live in the split epoch.

## What is proved

The Lean development is axiom-free. The main theorem,
`theory_of_everything` in [`ToE.lean`](ToE.lean), establishes:

1. There is a unified theory whose carrier has the infinity of `ℕ`.
2. After time, that theory splits into QFT and GR.
3. QFT has the infinity of the countable numbers.
4. GR has the infinity of the reals.
5. Those infinities are not equinumerous, so the split cannot be undone
   by identifying the two carriers.

Supporting facts live in:

- [`ToE/Infinity.lean`](ToE/Infinity.lean) — equinumerosity, Cantor’s
  diagonal argument, the two infinities
- [`ToE/Physics.lean`](ToE/Physics.lean) — unified theory, QFT, GR, and
  the split `separate`
- [`ToE/Cosmology.lean`](ToE/Cosmology.lean) — cosmic time, epochs,
  history
- [`ToE/Geometry.lean`](ToE/Geometry.lean) — Delone realization, holographic
  screens, causal order, and horizons that split a finite diamond into
  past, screen, and future

The continuum is taken as the Cantor space `ℕ → Bool`. Classically this
is equinumerous with `ℝ` (binary expansions, up to a countable set of
dyadic identifications, which do not change the cardinality).

## Geometry of the split

Cardinality says the carrier and the continuum are different infinities.
It does not say how one sits inside the other. After time, the countable
carrier is realized as a **Delone set** in GR spacetime
(`DeloneSplit` / `standardDelone`):

| Datum | Role |
|---|---|
| `realize` | injective embedding of QFT modes as events |
| `gap > 0` | uniform discreteness — a shortest distance between events |
| `coveringRadius > 0` | relative density — continuum holes are bounded |
| `density > 0` | points of the carrier per unit continuum volume |
| `newtonG = gap²` | Newton’s constant in units \(\hbar = c = 1\) |

A dense embedding (like \(\mathbb{Q}\subset\mathbb{R}\)) is a theorem of
the structure, not an extra axiom: it would force two events inside the
gap, so \(G\) would vanish. The standard model takes gap, covering
radius, and density all equal to `1` in lattice units, hence \(G = 1\)
in those units. The SI value still needs an identification of the
lattice unit with a metre; quasicrystalline cut-and-project geometry is
a later refinement that computes density from a window, not a replacement
for this layer.

## Holographic screens

Delone geometry makes \(G\) a conversion. A **holographic screen**
(`HolographicScreen` / `standardScreen`) is where that conversion counts:

\[
A = 4 N G
\]

in units \(\hbar = c = k_B = 1\). \(A\) is a finite continuum area; \(N\)
is a finite number of bits of the original countable carrier. The
information on the screen therefore injects into \(\mathbb{N}\) and cannot
carry the infinity of the reals — a finite-area horizon cannot hide a
continuum of independent quantum data.

On the standard realization, \(G = 1\) and a cell of area \(4\) holds
exactly one bit. The SI value of \(G\) still needs a metre; the area law
is already a theorem in lattice units.

## Causal order

The countable carrier is a causal set (`CausalSplit` /
`standardCausal`): a strict partial order with **finite open intervals**.
There is no injective copy of \(\mathbb{N}\) between two events, so the
time direction does not smuggle in a continuum of independent instants.

A **realized screen** (`RealizedScreen`) is a holographic screen whose
\(N\) bits are \(N\) pairwise incomparable carrier events — an antichain,
hence spacelike. A timelike chain of two or more events cannot be a
screen.

On the standard carrier `Nat`, \(a\) precedes \(b\) when \(a+2\le b\), so
immediate neighbours are spacelike. The one-bit cell is the event `0`.
The two-bit screen `{0,1}` has area `8` and is not a chain.

## Horizons

A **causal diamond** (`CausalDiamond`) is a finite region of the carrier.
A **horizon** (`Horizon` / `standardHorizon`) is a realized screen that is
**maximal in that diamond**: every diamond event is on the screen, in its
past, or in its future. The three classes are exclusive. Past and future
are subsets of a finite set, so neither can carry the infinity of the
reals — the interior cannot hide a continuum of independent information.

On the standard diamond `{0,…,6}`, the mid-slice `{2,3}` is a two-bit
horizon: past `{0,1}`, screen `{2,3}`, future `{4,5,6}`, still with
\(A = 8 = 4\cdot 2\cdot G\).

## Experimental predictions

The Lean development proves a cardinality split, not a Lagrangian. The
predictions below are the phenomenological consequences of taking that
split as physical: a countable unified origin, QFT still countable, GR
an emergent continuum, and no identification of the two infinities after
`t = 0`.

### 1. Spacetime is emergent, not fundamental

Continuum Lorentzian geometry is an after-time description. At
sufficiently high curvature or short distance — Planck scale, black-hole
interiors, the earliest universe — the continuum approximation fails and
the countable unified carrier is the right kinematics.

**Signature.** A shortest operational length/time (Planck scale). No
curvature singularity at the Big Bang: the origin is a first countable
instant, not a divergent metric. Trans-Planckian modes in the primordial
spectrum are absent or cut off, because they would be continuum labels
that the origin does not possess.

**Falsified by.** A past-eternal continuum spacetime with no discrete
first moment, or laboratory access to arbitrarily short spacetime
intervals with continuum GR still exact.

### 2. Primordial cosmology is the main experimental window

The unified theory exists only at `t = 0`. Every later time is split.
Collider unification of gravity with the Standard Model into a single
countable Fock space that *also* keeps continuum spacetime as
fundamental is not a prediction of this theory; it contradicts the
split.

**Signature.** A first moment in cosmic time. Discrete (or sharply cut
off) primordial mode sum, looking continuous at the scales of the CMB
acoustic peaks, with possible anomalies at the largest scales (lowest
multipoles) where the countability of the original carrier is least
washed out. A finite onset of inflation rather than past-eternal
inflation as a fundamental history.

**Falsified by.** Evidence for an infinite past of continuum spacetime
as the fundamental description, or a primordial spectrum that requires
an uncountable independent set of quantum modes.

### 3. Quantum theory stays separable; continuum labels belong to gravity

Constructive QFT on a countable mode set is the exact quantum kinematics,
not an approximation. Continuous spectra and continuous momenta are GR
labels (points of the emergent continuum), not extra quantum degrees of
freedom. Non-separable Hilbert spaces with a continuum of independent
modes are the wrong kinematics for matter.

**Signature.** Every laboratory quantum system has a countable
orthonormal basis. Apparent continuous spectra come from coupling to
spacetime (position, momentum as continuum eigenvalues), not from an
uncountable set of independent quantum observables. UV divergences in
QFT appear when mode labels are taken from GR’s continuum; they are
artifacts of borrowing the wrong infinity.

**Falsified by.** A physically required, non-separable matter Hilbert
space whose independent degrees of freedom are equinumerous with the
reals.

### 4. Gravity is not a particle theory of the same kind as QFT

Because GR carries the real infinity and QFT the countable infinity,
gravitons as ordinary Fock-space quanta are an effective description at
best. The fundamental gravitational kinematics are the continuum of
configurations of the countable carrier, not a second copy of that
carrier.

**Signature.** Gravitational waves exist (continuum geometry, already
observed). Absorption and emission that transfer energy to matter are
discrete, because the matter side is QFT. There is no fundamental
graviton number operator on the same footing as photon number. Black
hole entropy is finite for finite area and counts countable quantum
degrees of freedom, not spacetime points: the Bekenstein–Hawking formula
is a count of the original carrier accessible through a boundary, which
is why it is an area law rather than a bulk volume count of continuum
events.

**Falsified by.** A successful, fundamental Fock-space quantization of
the gravitational field in which gravitons are the same kind of countable
quanta as photons *and* spacetime remains a fundamental continuum of
independent events.

### 5. The information paradox is a clash of infinities

Hawking radiation is QFT (countable). The geometric black-hole interior
is GR (continuum). Information is a quantum resource, so its capacity is
countable. A black hole cannot hide a continuum-worth of independent
information behind a finite-area horizon.

**Signature.** Page curve: information returns in the radiation.
Remnants or baby universes that store uncountably much information are
forbidden. The interior continuum description is not a second,
independent set of degrees of freedom over and above the countable
carrier.

**Falsified by.** A consistent accounting in which a finite-area horizon
hides a continuum of independent quantum information.

### 6. Laboratory gravity remains split from laboratory QFT

We are at `t > 0`. Precision tests of GR (light deflection, Shapiro
delay, gravitational waves, clocks in gravitational potentials) should
continue to see continuum differential geometry. Precision tests of QFT
should continue to see countable spectra, discrete quanta, and separable
Hilbert spaces. Unification is cosmological and historical, not a
high-energy identification we can restore by turning up a collider.

**Signature.** No threshold energy at which gravity becomes just another
gauge field with a countable particle spectrum while spacetime stays a
fundamental continuum. Effective field theory of gravitons may work as
an approximation, then fail for the reason above: the infinities do not
match.

**Falsified by.** An experimental regime in which gravity and the
Standard Model are the same countable particle theory and continuum
spacetime is still fundamental, not emergent.

## Falsification in one line

The theory is wrong if, after the origin, QFT and GR can be identified
as carriers of the same infinity — either both countable, or both
continuum — while still describing quantum quanta and spacetime
geometry.

## Building

Requires [elan](https://github.com/leanprover/elan) / Lean 4.33.1 (see
`lean-toolchain`).

```bash
lake build
```

## License

MIT. See [LICENSE](LICENSE).
