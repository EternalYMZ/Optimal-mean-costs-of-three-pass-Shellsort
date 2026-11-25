import Shellsort.F09CertificateLowerJ3d2A
import Shellsort.F09CertificateLowerJ3d2B
import Shellsort.F09CertificateLowerJ3d2C
import Shellsort.F09CertificateLowerJ3d2D

namespace Shellsort.F09.Quad.LowerJ3d2
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 55134587001, 63395781436, 70577892822, 76983773754, 82794054057, 88126893320, 93064693584, 97667693260, 101981553487, 106041896233, 109877170475, 113510543366, 116961193852, 120245224683, 123376322140, 126366243964, 129225187252, 131962070614, 134584753820, 137100211135, 139514669727, 141833721424, 144062413827, 146205325268, 148266626981, 150250135060, 152159354148, 153997514426, 155767603071, 157472391154, 159114456733, 160696204764, 162219884353, 163687603761, 165101343559, 166462968229, 167774236491, 169036810605, 170252264823, 171422093173, 172547716685, 173630490162, 174671708550, 175672612946, 176634396247, 177558208451, 178445161583, 179296334223, 180112775637, 180895509461, 181645536950, 182363839786, 183051382422, 183709114015, 184337969929, 184938872856, 185512733583, 186060451428, 186582914405, 187080999139, 187555570576, 188007481535, 188437572120, 188846669053, 189235584935, 189605117474, 189956048712, 190289144254, 190605152540, 190904804151, 191188811185, 191457866692, 191712644183, 191953797226, 192181959109, 192397742597, 192601739761, 192794521888, 192976639467, 193148622249, 193310979365, 193464199518, 193608751228, 193745083121, 193873624278, 193994784615, 194108955306, 194216509228, 194317801439, 194413169676, 194502934865, 194587401650, 194666858920, 194741580353, 194811824951, 194877837577, 194939849489, 194998078860, 195052731294, 195104000330, 195152067924, 195197104927, 195239271535, 195278717729, 195315583682, 195350000161, 195382088894, 195411962915, 195439726889, 195465477405, 195489303246, 195511285626, 195531498401, 195550008244, 195566874792, 195582150751, 195595881968, 195608107459, 195618859397, 195628163044, 195636036645, 195642491248, 195647530475, 195651150212, 195653338229, 195654073701]

theorem knot : (((1866811/12500000:ℚ):ℚ):ℝ) ≤ J (1/(((3/2:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (4/9:ℚ) (left i) (scores[i.val]?.getD 0) := by
    intro i
    fin_cases i
    · exact row000
    · exact row001
    · exact row002
    · exact row003
    · exact row004
    · exact row005
    · exact row006
    · exact row007
    · exact row008
    · exact row009
    · exact row010
    · exact row011
    · exact row012
    · exact row013
    · exact row014
    · exact row015
    · exact row016
    · exact row017
    · exact row018
    · exact row019
    · exact row020
    · exact row021
    · exact row022
    · exact row023
    · exact row024
    · exact row025
    · exact row026
    · exact row027
    · exact row028
    · exact row029
    · exact row030
    · exact row031
    · exact row032
    · exact row033
    · exact row034
    · exact row035
    · exact row036
    · exact row037
    · exact row038
    · exact row039
    · exact row040
    · exact row041
    · exact row042
    · exact row043
    · exact row044
    · exact row045
    · exact row046
    · exact row047
    · exact row048
    · exact row049
    · exact row050
    · exact row051
    · exact row052
    · exact row053
    · exact row054
    · exact row055
    · exact row056
    · exact row057
    · exact row058
    · exact row059
    · exact row060
    · exact row061
    · exact row062
    · exact row063
    · exact row064
    · exact row065
    · exact row066
    · exact row067
    · exact row068
    · exact row069
    · exact row070
    · exact row071
    · exact row072
    · exact row073
    · exact row074
    · exact row075
    · exact row076
    · exact row077
    · exact row078
    · exact row079
    · exact row080
    · exact row081
    · exact row082
    · exact row083
    · exact row084
    · exact row085
    · exact row086
    · exact row087
    · exact row088
    · exact row089
    · exact row090
    · exact row091
    · exact row092
    · exact row093
    · exact row094
    · exact row095
    · exact row096
    · exact row097
    · exact row098
    · exact row099
    · exact row100
    · exact row101
    · exact row102
    · exact row103
    · exact row104
    · exact row105
    · exact row106
    · exact row107
    · exact row108
    · exact row109
    · exact row110
    · exact row111
    · exact row112
    · exact row113
    · exact row114
    · exact row115
    · exact row116
    · exact row117
    · exact row118
    · exact row119
    · exact row120
    · exact row121
    · exact row122
    · exact row123
    · exact row124
    · exact row125
    · exact row126
    · exact row127
    · exact row128
  have h := lower_of_rows (lam:=(4/9:ℚ)) (target:=(1866811/12500000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ3d2
