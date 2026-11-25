import Shellsort.F09CertificateLowerJ1d2A
import Shellsort.F09CertificateLowerJ1d2B
import Shellsort.F09CertificateLowerJ1d2C
import Shellsort.F09CertificateLowerJ1d2D

namespace Shellsort.F09.Quad.LowerJ1d2
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 55137868735, 77001631513, 93111968103, 106134990250, 117116957809, 126601181542, 134914398517, 142272120339, 148825898407, 154687459041, 159942206534, 164657290243, 168886658646, 172674386041, 176057062817, 179065743637, 181727679355, 184067837655, 186110110754, 187878120341, 189395604650, 190686448462, 191774460772, 192683012986, 193434634249, 194050633715, 194550792256, 194953143578, 195273848282, 195527153938, 195725428187, 195879249277, 195997538052, 196087716445, 196155879493, 196206970214, 196244949168, 196272952877, 196293437371, 196308304922, 196319013385, 196326668621, 196332101194, 196335928922, 196338607097, 196340468218, 196341752984, 196342634166, 196343234753, 196343641604, 196343915589, 196344099043, 196344221201, 196344302110, 196344355423, 196344390378, 196344413189, 196344428007, 196344437591, 196344443764, 196344447725, 196344450257, 196344451869, 196344452893, 196344453542, 196344453951, 196344454208, 196344454370, 196344454471, 196344454535, 196344454574, 196344454599, 196344454615, 196344454624, 196344454630, 196344454634, 196344454636, 196344454638, 196344454638, 196344454639, 196344454639, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640, 196344454640]

theorem knot : (((15594707/100000000:ℚ):ℚ):ℝ) ≤ J (1/(((1/2:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (4:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(4:ℚ)) (target:=(15594707/100000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ1d2
