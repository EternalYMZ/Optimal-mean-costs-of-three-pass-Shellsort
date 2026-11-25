import Shellsort.F09CertificateRows

/-! Finite row witnesses for the signed Fourier quadrature. -/
namespace Shellsort.F09.Quad.LowerJ1d2
open Shellsort.F09.Eval
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def seed064 : Box := ⟨46105053340103419266639624992429496335353,46105053340103431201267802845316271317733⟩
private def modes064 : Array Box := #[⟨46105053340103419266639624992429496335353,46105053340103431201267802845316271317734⟩, ⟨1447425423258642272,1447425423258643772⟩]

theorem row064 : RowCert false (4:ℚ) 8192 196344452893 := by
  change _ ≤ rowValue false (4:ℚ) 8192 * scoreScale
  rw [row_cached (d:=(7/16:ℚ)) (seed:=seed064) (es:=modes064)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed065 : Box := ⟨28994839490376114663215302441628100916223,28994839490376122577160502678102538701369⟩
private def modes065 : Array Box := #[⟨28994839490376114663215302441628100916223,28994839490376122577160502678102538701370⟩, ⟨226404428253828003,226404428253828251⟩]

theorem row065 : RowCert false (4:ℚ) 8450 196344453542 := by
  change _ ≤ rowValue false (4:ℚ) 8450 * scoreScale
  rw [row_cached (d:=(120594175/268435456:ℚ)) (seed:=seed065) (es:=modes065)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed066 : Box := ⟨18194722055253836996049718014145486272395,18194722055253842226509276751563296255180⟩
private def modes066 : Array Box := #[⟨18194722055253836996049718014145486272395,18194722055253842226509276751563296255181⟩, ⟨35106196860895592,35106196860895634⟩]

theorem row066 : RowCert false (4:ℚ) 8712 196344453951 := by
  change _ ≤ rowValue false (4:ℚ) 8712 * scoreScale
  rw [row_cached (d:=(7735167/16777216:ℚ)) (seed:=seed066) (es:=modes066)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed067 : Box := ⟨11395229709078673903736124264328656882967,11395229709078677350099543641579127667333⟩
private def modes067 : Array Box := #[⟨11395229709078673903736124264328656882967,11395229709078677350099543641579127667334⟩, ⟨5401251729175418,5401251729175426⟩]

theorem row067 : RowCert false (4:ℚ) 8978 196344454208 := by
  change _ ≤ rowValue false (4:ℚ) 8978 * scoreScale
  rw [row_cached (d:=(126944431/268435456:ℚ)) (seed:=seed067) (es:=modes067)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed068 : Box := ⟨7124520214395023467394536369767818213806,7124520214395025731879342361388919632080⟩
private def modes068 : Array Box := #[⟨7124520214395023467394536369767818213806,7124520214395025731879342361388919632081⟩, ⟨825324188244911,825324188244913⟩]

theorem row068 : RowCert false (4:ℚ) 9248 196344454370 := by
  change _ ≤ rowValue false (4:ℚ) 9248 * scoreScale
  rw [row_cached (d:=(508351/1048576:ℚ)) (seed:=seed068) (es:=modes068)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed069 : Box := ⟨4447812930373349494994247785938755565178,4447812930373350979146829950787852291608⟩
private def modes069 : Array Box := #[⟨4447812930373349494994247785938755565178,4447812930373350979146829950787852291609⟩, ⟨125368414507641,125368414507642⟩]

theorem row069 : RowCert false (4:ℚ) 9522 196344454471 := by
  change _ ≤ rowValue false (4:ℚ) 9522 * scoreScale
  rw [row_cached (d:=(133341327/268435456:ℚ)) (seed:=seed069) (es:=modes069)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed070 : Box := ⟨2773324947542340764132793447047766902819,2773324947542341734649897214056070130921⟩
private def modes070 : Array Box := #[⟨2773324947542340764132793447047766902819,2773324947542341734649897214056070130922⟩, ⟨18949821124049,18949821124050⟩]

theorem row070 : RowCert false (4:ℚ) 9800 196344454535 := by
  change _ ≤ rowValue false (4:ℚ) 9800 * scoreScale
  rw [row_cached (d:=(8534575/16777216:ℚ)) (seed:=seed070) (es:=modes070)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed071 : Box := ⟨1727527207385944151788183003269932808460,1727527207385944785160493723856724096629⟩
private def modes071 : Array Box := #[⟨1727527207385944151788183003269932808460,1727527207385944785160493723856724096630⟩, ⟨2852999299785,2852999299786⟩]

theorem row071 : RowCert false (4:ℚ) 10082 196344454574 := by
  change _ ≤ rowValue false (4:ℚ) 10082 * scoreScale
  rw [row_cached (d:=(139771807/268435456:ℚ)) (seed:=seed071) (es:=modes071)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed072 : Box := ⟨1075293438166668812370863276017252529688,1075293438166669225002946659473504670055⟩
private def modes072 : Array Box := #[⟨1075293438166668812370863276017252529688,1075293438166669225002946659473504670056⟩, ⟨428262515539,428262515540⟩]

theorem row072 : RowCert false (4:ℚ) 10368 196344454599 := by
  change _ ≤ rowValue false (4:ℚ) 10368 * scoreScale
  rw [row_cached (d:=(34911/65536:ℚ)) (seed:=seed072) (es:=modes072)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed073 : Box := ⟨668985431232305610368808742009943434393,668985431232305878799913677583716392137⟩
private def modes073 : Array Box := #[⟨668985431232305610368808742009943434393,668985431232305878799913677583716392138⟩, ⟨64160645048,64160645049⟩]

theorem row073 : RowCert false (4:ℚ) 10658 196344454615 := by
  change _ ≤ rowValue false (4:ℚ) 10658 * scoreScale
  rw [row_cached (d:=(146222431/268435456:ℚ)) (seed:=seed073) (es:=modes073)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed074 : Box := ⟨416107003077312756399916484567512883578,416107003077312930816432531150014534969⟩
private def modes074 : Array Box := #[⟨416107003077312756399916484567512883578,416107003077312930816432531150014534970⟩, ⟨9603337265,9603337266⟩]

theorem row074 : RowCert false (4:ℚ) 10952 196344454624 := by
  change _ ≤ rowValue false (4:ℚ) 10952 * scoreScale
  rw [row_cached (d:=(9340687/16777216:ℚ)) (seed:=seed074) (es:=modes074)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed075 : Box := ⟨258824127719224141801653549109945269144,258824127719224255027980358770173909662⟩
private def modes075 : Array Box := #[⟨258824127719224141801653549109945269144,258824127719224255027980358770173909663⟩, ⟨1437543904,1437543905⟩]

theorem row075 : RowCert false (4:ℚ) 11250 196344454630 := by
  change _ ≤ rowValue false (4:ℚ) 11250 * scoreScale
  rw [row_cached (d:=(152679375/268435456:ℚ)) (seed:=seed075) (es:=modes075)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed076 : Box := ⟨161038628641902188361850412941426697770,161038628641902261818909813558949115120⟩
private def modes076 : Array Box := #[⟨161038628641902188361850412941426697770,161038628641902261818909813558949115121⟩, ⟨215438013,215438014⟩]

theorem row076 : RowCert false (4:ℚ) 11552 196344454634 := by
  change _ ≤ rowValue false (4:ℚ) 11552 * scoreScale
  rw [row_cached (d:=(609007/1048576:ℚ)) (seed:=seed076) (es:=modes076)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed077 : Box := ⟨100252837384196875322776688104620882957,100252837384196922962408407362346894401⟩
private def modes077 : Array Box := #[⟨100252837384196875322776688104620882957,100252837384196922962408407362346894402⟩, ⟨32358529,32358530⟩]

theorem row077 : RowCert false (4:ℚ) 11858 196344454636 := by
  change _ ≤ rowValue false (4:ℚ) 11858 * scoreScale
  rw [row_cached (d:=(159128431/268435456:ℚ)) (seed:=seed077) (es:=modes077)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed078 : Box := ⟨62462858432202029855133518305869597588,62462858432202060749236667941331468684⟩
private def modes078 : Array Box := #[⟨62462858432202029855133518305869597588,62462858432202060749236667941331468685⟩, ⟨4876289,4876290⟩]

theorem row078 : RowCert false (4:ℚ) 12168 196344454638 := by
  change _ ≤ rowValue false (4:ℚ) 12168 * scoreScale
  rw [row_cached (d:=(10146591/16777216:ℚ)) (seed:=seed078) (es:=modes078)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed079 : Box := ⟨38960489841023108561343754236870690801,38960489841023128600522722418811103574⟩
private def modes079 : Array Box := #[⟨38960489841023108561343754236870690801,38960489841023128600522722418811103575⟩, ⟨738073,738074⟩]

theorem row079 : RowCert false (4:ℚ) 12482 196344454638 := by
  change _ ≤ rowValue false (4:ℚ) 12482 * scoreScale
  rw [row_cached (d:=(165555007/268435456:ℚ)) (seed:=seed079) (es:=modes079)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed080 : Box := ⟨24334625549959442998001419414550983336,24334625549959456002912569921727683711⟩
private def modes080 : Array Box := #[⟨24334625549959442998001419414550983336,24334625549959456002912569921727683712⟩, ⟨112331,112332⟩]

theorem row080 : RowCert false (4:ℚ) 12800 196344454639 := by
  change _ ≤ rowValue false (4:ℚ) 12800 * scoreScale
  rw [row_cached (d:=(2575/4096:ℚ)) (seed:=seed080) (es:=modes080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed081 : Box := ⟨15224551188522719755684101468720938430,15224551188522728202347812482703644721⟩
private def modes081 : Array Box := #[⟨15224551188522719755684101468720938430,15224551188522728202347812482703644722⟩, ⟨17209,17210⟩]

theorem row081 : RowCert false (4:ℚ) 13122 196344454639 := by
  change _ ≤ rowValue false (4:ℚ) 13122 * scoreScale
  rw [row_cached (d:=(171944127/268435456:ℚ)) (seed:=seed081) (es:=modes081)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed082 : Box := ⟨9543491694626322767453726094098110277,9543491694626328259596387009317963026⟩
private def modes082 : Array Box := #[⟨9543491694626322767453726094098110277,9543491694626328259596387009317963027⟩, ⟨2657,2658⟩]

theorem row082 : RowCert false (4:ℚ) 13448 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 13448 * scoreScale
  rw [row_cached (d:=(10944991/16777216:ℚ)) (seed:=seed082) (es:=modes082)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed083 : Box := ⟨5995673890506781773601976103754771481,5995673890506785349679188633333280700⟩
private def modes083 : Array Box := #[⟨5995673890506781773601976103754771481,5995673890506785349679188633333280701⟩, ⟨413,414⟩]

theorem row083 : RowCert false (4:ℚ) 13778 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 13778 * scoreScale
  rw [row_cached (d:=(178280431/268435456:ℚ)) (seed:=seed083) (es:=modes083)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed084 : Box := ⟨3776270303860925577206283461685105776,3776270303860927909651027046144022908⟩
private def modes084 : Array Box := #[⟨3776270303860925577206283461685105776,3776270303860927909651027046144022909⟩, ⟨65,66⟩]

theorem row084 : RowCert false (4:ℚ) 14112 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 14112 * scoreScale
  rw [row_cached (d:=(708687/1048576:ℚ)) (seed:=seed084) (es:=modes084)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed085 : Box := ⟨2385121504099533520439001896954675312,2385121504099535044798577242584244279⟩
private def modes085 : Array Box := #[⟨2385121504099533520439001896954675312,2385121504099535044798577242584244280⟩, ⟨10,11⟩]

theorem row085 : RowCert false (4:ℚ) 14450 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 14450 * scoreScale
  rw [row_cached (d:=(184548175/268435456:ℚ)) (seed:=seed085) (es:=modes085)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed086 : Box := ⟨1511157871278528304528272528821663571,1511157871278529303075274213124292154⟩
private def modes086 : Array Box := #[⟨1511157871278528304528272528821663571,1511157871278529303075274213124292155⟩, ⟨1,2⟩]

theorem row086 : RowCert false (4:ℚ) 14792 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 14792 * scoreScale
  rw [row_cached (d:=(11728207/16777216:ℚ)) (seed:=seed086) (es:=modes086)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed087 : Box := ⟨960709589454874175082045521614925230,960709589454874830909130318350798652⟩
private def modes087 : Array Box := #[⟨960709589454874175082045521614925230,960709589454874830909130318350798653⟩, ⟨0,1⟩]

theorem row087 : RowCert false (4:ℚ) 15138 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 15138 * scoreScale
  rw [row_cached (d:=(190731231/268435456:ℚ)) (seed:=seed087) (es:=modes087)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed088 : Box := ⟨613041631741301133311932390282152993,613041631741301565314102403351002065⟩
private def modes088 : Array Box := #[⟨613041631741301133311932390282152993,613041631741301565314102403351002066⟩, ⟨0,1⟩]

theorem row088 : RowCert false (4:ℚ) 15488 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 15488 * scoreScale
  rw [row_cached (d:=(47311/65536:ℚ)) (seed:=seed088) (es:=modes088)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed089 : Box := ⟨392769264396401347402638219812540672,392769264396401632895681750022508130⟩
private def modes089 : Array Box := #[⟨392769264396401347402638219812540672,392769264396401632895681750022508131⟩, ⟨0,1⟩]

theorem row089 : RowCert false (4:ℚ) 15842 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 15842 * scoreScale
  rw [row_cached (d:=(196813087/268435456:ℚ)) (seed:=seed089) (es:=modes089)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed090 : Box := ⟨252737897498854565843545363178335769,252737897498854755189801479746356718⟩
private def modes090 : Array Box := #[⟨252737897498854565843545363178335769,252737897498854755189801479746356719⟩, ⟨0,1⟩]

theorem row090 : RowCert false (4:ℚ) 16200 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 16200 * scoreScale
  rw [row_cached (d:=(12488175/16777216:ℚ)) (seed:=seed090) (es:=modes090)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed091 : Box := ⟨163390116521190964126303463092638634,163390116521191090195610239926989619⟩
private def modes091 : Array Box := #[⟨163390116521190964126303463092638634,163390116521191090195610239926989620⟩, ⟨0,1⟩]

theorem row091 : RowCert false (4:ℚ) 16562 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 16562 * scoreScale
  rw [row_cached (d:=(202776847/268435456:ℚ)) (seed:=seed091) (es:=modes091)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed092 : Box := ⟨106155491589903257750527128849065989,106155491589903342044129752526268978⟩
private def modes092 : Array Box := #[⟨106155491589903257750527128849065989,106155491589903342044129752526268979⟩, ⟨0,1⟩]

theorem row092 : RowCert false (4:ℚ) 16928 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 16928 * scoreScale
  rw [row_cached (d:=(803551/1048576:ℚ)) (seed:=seed092) (es:=modes092)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed093 : Box := ⟨69336302638229373354002033880806077,69336302638229429972055376786447610⟩
private def modes093 : Array Box := #[⟨69336302638229373354002033880806077,69336302638229429972055376786447611⟩, ⟨0,1⟩]

theorem row093 : RowCert false (4:ℚ) 17298 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 17298 * scoreScale
  rw [row_cached (d:=(208605231/268435456:ℚ)) (seed:=seed093) (es:=modes093)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed094 : Box := ⟨45543060959935386103071462992510576,45543060959935424318090475470921117⟩
private def modes094 : Array Box := #[⟨45543060959935386103071462992510576,45543060959935424318090475470921118⟩, ⟨0,1⟩]

theorem row094 : RowCert false (4:ℚ) 17672 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 17672 * scoreScale
  rw [row_cached (d:=(13216447/16777216:ℚ)) (seed:=seed094) (es:=modes094)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed095 : Box := ⟨30093340830872808386202810680137316,30093340830872834314686734202139029⟩
private def modes095 : Array Box := #[⟨30093340830872808386202810680137316,30093340830872834314686734202139030⟩, ⟨0,1⟩]

theorem row095 : RowCert false (4:ℚ) 18050 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 18050 * scoreScale
  rw [row_cached (d:=(214280575/268435456:ℚ)) (seed:=seed095) (es:=modes095)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end Shellsort.F09.Quad.LowerJ1d2
