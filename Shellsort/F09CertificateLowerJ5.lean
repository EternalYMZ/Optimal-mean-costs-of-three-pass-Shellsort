import Shellsort.F09CertificateLowerJ5A
import Shellsort.F09CertificateLowerJ5B
import Shellsort.F09CertificateLowerJ5C
import Shellsort.F09CertificateLowerJ5D

namespace Shellsort.F09.Quad.LowerJ5
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55097213813, 57705395747, 60185839734, 62553585897, 64820837003, 66997656519, 69092460165, 71112371081, 73063482186, 74951053782, 76779664913, 78553331073, 80275596977, 81949610559, 83578182657, 85163835613, 86708843216, 88215263801, 89684967880, 91119661376, 92520905277, 93890132376, 95228661590, 96537710291, 97818404962, 99071790450, 100298838046, 101500452552, 102677478497, 103830705623, 104960873734, 106068677007, 107154767833, 108219760236, 109264232951, 110288732170, 111293774030, 112279846841, 113247413109, 114196911370, 115128757844, 116043347950, 116941057680, 117822244848, 118687250244, 119536398673, 120369999919, 121188349628, 121991730108, 122780411081, 123554650361, 124314694482, 125060779283, 125793130438, 126511963950, 127217486607, 127909896401, 128589382916, 129256127685, 129910304518, 130552079813, 131181612828, 131799055944, 132404554901, 132998249015, 133580271379, 134150749044, 134709803184, 135257549248, 135794097094, 136319551110, 136834010326, 137337568504, 137830314223, 138312330949, 138783697097, 139244486072, 139694766313, 140134601310, 140564049626, 140983164893, 141391995810, 141790586123, 142178974594, 142557194960, 142925275886, 143283240894, 143631108295, 143968891097, 144296596905, 144614227810, 144921780261, 145219244923, 145506606524, 145783843677, 146050928700, 146307827403, 146554498866, 146790895197, 147016961260, 147232634394, 147437844098, 147632511689, 147816549940, 147989862685, 148152344382, 148303879659, 148444342801, 148573597214, 148691494834, 148797875482, 148892566182, 148975380401, 149046117237, 149104560533, 149150477908, 149183619712, 149203717876, 149210484663]

theorem knot : (((5309131/50000000:ℚ):ℚ):ℝ) ≤ J (1/(((5:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (1/25:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(1/25:ℚ)) (target:=(5309131/50000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ5
