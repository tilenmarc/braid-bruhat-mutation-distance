import OMDistance.Signotope
import OMDistance.Lift
import BraidDistance.Construction

/-!
# The instances of Sections 7 and 8

Trusted definitions.  For a graph `G` (Part I, `BraidDistance.Graph`) with `m = 3n + |E|` wires, Part I defines the
sign vectors `s_G = sG G` and `v_G = vG G` of the words `W^s_G`, `W^v_G` (Section 4).  Here they are viewed as
rank-3 sign maps on `[m]`:

* `sMap G = s_G`, `vMap G = v_G` (via `ofSMap`);
* rank 3 (Section 7): the chirotopes `Pos₃(s_G) = posF m (sMap G)` and `Pos₃(v_G) = posF m (vMap G)` on
  `[m] ∪ {∞} = [m+1]`;
* higher rank (Section 8): with `c` new elements, the lifts `L s_G = lift c (sMap G)` and `L v_G = lift c (vMap G)`
  on `N ∪ S = [c+m]`, and their positive fibres `Pos_r(L s_G) = posF (c+m) (lift c (sMap G))` on
  `N ∪ S ∪ {∞} = [c+m+1]`.
-/

namespace OMDistance

open BraidDistance

/-- `s_G` as a rank-3 sign map on `[m]`. -/
def sMap (G : Graph) : SignMap := ofSMap (sG G)

/-- `v_G` as a rank-3 sign map on `[m]`. -/
def vMap (G : Graph) : SignMap := ofSMap (vG G)

end OMDistance
