import Shellsort.F09CertificateLowerJ3A
import Shellsort.F09CertificateLowerJ3B
import Shellsort.F09CertificateLowerJ3C
import Shellsort.F09CertificateLowerJ3D

namespace Shellsort.F09.Quad.LowerJ3
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 0, 0, 0, 55123506593, 59410653192, 63373317366, 67068865276, 70539137470, 73815774846, 76923401826, 79881635056, 82706407654, 85410874264, 88006048597, 90501264223, 92904515083, 95222712031, 97461879411, 99627307982, 101723675474, 103755142799, 105725431659, 107637887769, 109495532844, 111301107672, 113057108105, 114765815312, 116429321401, 118049551226, 119628281067, 121167154707, 122667697332, 124131327621, 125559368280, 126953055278, 128313545973, 129641926271, 130939216978, 132206379430, 133444320518, 134653897173, 135835920382, 136991158801, 138120341999, 139224163394, 140303282901, 141358329333, 142389902585, 143398575615, 144384896251, 145349388842, 146292555764, 147214878799, 148116820402, 148998824862, 149861319366, 150704714981, 151529407559, 152335778569, 153124195861, 153895014381, 154648576821, 155385214222, 156105246541, 156808983157, 157496723359, 158168756782, 158825363817, 159466815992, 160093376317, 160705299613, 161302832805, 161886215197, 162455678731, 163011448211, 163553741524, 164082769829, 164598737740, 165101843480, 165592279032, 166070230265, 166535877049, 166989393355, 167430947342, 167860701423, 168278812333, 168685431162, 169080703394, 169464768920, 169837762040, 170199811457, 170551040247, 170891565824, 171221499883, 171540948335, 171850011222, 172148782616, 172437350505, 172715796660, 172984196483, 173242618842, 173491125877, 173729772799, 173958607654, 174177671076, 174386996008, 174586607402, 174776521888, 174956747422, 175127282893, 175288117704, 175439231314, 175580592740, 175712160024, 175833879643, 175945685880, 176047500140, 176139230198, 176220769395, 176291995756, 176352771034, 176402939668, 176442327648, 176470741278, 176487965821, 176493764024]

theorem knot : (((6400487/50000000:ℚ):ℚ):ℝ) ≤ J (1/(((3:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (1/9:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(1/9:ℚ)) (target:=(6400487/50000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ3
