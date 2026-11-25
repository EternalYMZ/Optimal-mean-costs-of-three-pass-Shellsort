import Shellsort.F09CertificateLowerJ2A
import Shellsort.F09CertificateLowerJ2B
import Shellsort.F09CertificateLowerJ2C
import Shellsort.F09CertificateLowerJ2D

namespace Shellsort.F09.Quad.LowerJ2
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 0, 55131714977, 61442719282, 67091067872, 72232323450, 76968136899, 81369318809, 85487575171, 89362053854, 93023258941, 96495521891, 99798631379, 102948947675, 105960187966, 108843994206, 111610352916, 114267911585, 116824221226, 119285925135, 121658907768, 123948413595, 126159143013, 128295330520, 130360809003, 132359063052, 134293273496, 136166354880, 137980987198, 139739642923, 141444610168, 143098012625, 144701826814, 146257897086, 147767948703, 149233599311, 150656369020, 152037689309, 153378910895, 154681310726, 155946098206, 157174420744, 158367368718, 159525979937, 160651243637, 161744104090, 162805463873, 163836186820, 164837100722, 165808999784, 166752646889, 167668775679, 168558092481, 169421278106, 170258989518, 171071861405, 171860507645, 172625522698, 173367482900, 174086947687, 174784460750, 175460551100, 176115734080, 176750512292, 177365376452, 177960806187, 178537270745, 179095229644, 179635133250, 180157423288, 180662533287, 181150888959, 181622908529, 182079002991, 182519576329, 182945025677, 183355741438, 183752107363, 184134500595, 184503291671, 184858844512, 185201516373, 185531657785, 185849612467, 186155717239, 186450301912, 186733689177, 187006194487, 187268125931, 187519784115, 187761462035, 187993444956, 188216010286, 188429427465, 188633957842, 188829854569, 189017362486, 189196718014, 189368149053, 189531874878, 189688106031, 189837044221, 189978882214, 190113803727, 190241983307, 190363586211, 190478768275, 190587675766, 190690445230, 190787203312, 190878066565, 190963141234, 191042523008, 191116296756, 191184536210, 191247303625, 191304649389, 191356611579, 191403215471, 191444472982, 191480382040, 191510925879, 191536072247, 191555772509, 191569960643, 191578552116, 191581442606]

theorem knot : (((7134197/50000000:ℚ):ℚ):ℝ) ≤ J (1/(((2:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (1/4:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(1/4:ℚ)) (target:=(7134197/50000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ2
