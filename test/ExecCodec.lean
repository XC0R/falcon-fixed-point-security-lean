import FalconPrecision.Exec.CodecKat
import FalconPrecision.Exec.WitnessData
import ExecRound3

/-! `FalconPrecision.Exec.Codec`, `.Verify`, `.CodecKat`: bit orders, fields, Compress/Decompress
on small inputs; entry 0 of the round-3 `falcon512-KAT.rsp` (sha256 `dd75c946…7354b5cd`) passes
`entryOkB`; HashToPoint on entries 0 and 70 equals `wC0`, `wC70` (Python `hashlib`); the 15
correctness theorems of `Codec` and `Verify`, and `entryOk_of`, `entriesOk_of`, depend only on the
standard axioms. -/

open FalconPrecision.Exec.Codec FalconPrecision.Exec.Witness

-- `0x01` is `[f,f,f,f,f,f,f,t]` most significant bit first and `[t,f,…]` least significant first;
-- a 14-bit field round-trips in both orders; the minimal 6-bit value is rejected
/-- info: true -/
#guard_msgs in
#eval bytesBits .msbFirst [0x01] = [false, false, false, false, false, false, false, true] &&
  bytesBits .lsbFirst [0x01] = [true, false, false, false, false, false, false, false] &&
  bitsBytes .lsbFirst [true, true] = [0x03] && bitsBytes .msbFirst [true, true] = [0xC0] &&
  fieldNat .lsbFirst (natField .lsbFirst 14 12288) = 12288 &&
  fieldNat .msbFirst (natField .msbFirst 14 12288) = 12288 &&
  (signedFields .msbFirst 6 1 (intField .msbFirst 6 (-32))).isNone &&
  signedFields .lsbFirst 6 2 (intField .lsbFirst 6 (-31) ++ intField .lsbFirst 6 31) =
    some [-31, 31]

-- Alg. 17: `0` is `0 0000000 1`, `-129` is `1 0000001 01`; Alg. 18 inverts it, rejects `-0`,
-- nonzero padding, a wrong length; the bound `2047` rejects `2048`, the spec's algorithms do not
/-- info: true -/
#guard_msgs in
#eval compress none [0, -129] 24 = some ([false, false, false, false, false, false, false, false,
    true, true, false, false, false, false, false, false, true, false, true] ++
    List.replicate 5 false) &&
  ((compress none [0, -129] 24).bind fun s => decompress none 2 s 24) = some [0, -129] &&
  (decompress none 1 ([true] ++ List.replicate 7 false ++ [true]) 9).isNone &&
  (decompress none 1 (List.replicate 8 false ++ [true, true]) 10).isNone &&
  (decompress none 1 (List.replicate 8 false ++ [true]) 10).isNone &&
  (compress (some 2047) [2048] 32).isNone &&
  ((compress none [2048] 32).bind fun s => decompress none 1 s 32) = some [2048] &&
  ((compress none [2048] 32).bind fun s => decompress (some 2047) 1 s 32).isNone

-- a toy degree-4 instance, both bit orders: keys and signatures round-trip
/-- info: true -/
#guard_msgs in
#eval [BitOrder.msbFirst, .lsbFirst].all fun o =>
  let C : EncChoices := { round3 with order := o, logn := 2, trLen := 3, sigPad := .fixed 52 }
  let k : SkData := ⟨[1, -31, 0, 5], [-1, 2, 31, -7], [127, -127, 0, 1], [7, 8, 9]⟩
  decodePk C (encodePk C [0, 12288, 5, 77]) = some [0, 12288, 5, 77] &&
    decodeSk C (encodeSk C k) = some k &&
    (encodeSig C ⟨List.replicate 40 3, [0, -129, 300, 1]⟩).bind (decodeSig C) =
      some ⟨List.replicate 40 3, [0, -129, 300, 1]⟩ &&
    (encodeSig { C with sigComp := .uncompressed } ⟨List.replicate 40 3, [0, -2047, 2047, 1]⟩).bind
      (decodeSig { C with sigComp := .uncompressed }) =
      some ⟨List.replicate 40 3, [0, -2047, 2047, 1]⟩ &&
    (encodeSm C (List.replicate 40 3) [1, 2] [0, -129, 300, 1]).bind (decodeSm C) =
      some (List.replicate 40 3, [1, 2], [0, -129, 300, 1])

/-- Entry 0 of `falcon512-KAT.rsp`: `msg`. -/
def kat0Msg : String := "D81C4D8D734FCBFBEADE3D3F8A039FAA2A2C9957E835AD55B22E75BF57BB556AC8"

/-- Entry 0 of `falcon512-KAT.rsp`: `sm`. -/
def kat0Sm : String := String.join [
  "026833B3C07507E4201748494D832B6EE2A6C93BFF9B0EE343B550D1F85A3D0DE0D704C6D17842951309D81C",
  "4D8D734FCBFBEADE3D3F8A039FAA2A2C9957E835AD55B22E75BF57BB556AC8290765843D1E460D17A527D2BC",
  "A405BD55BBC7DA09A8C620BE0AF4A767D9DB96B80F55E466676751EAABA7B93B86D71132DAA0EB376782B9EE",
  "E37519CE10FDD33FE9F29312C31D8736206D165CF4C528AA3DDC017845E1F0DD5B0A44FF961C42D874A95533",
  "E5B438982F524CA954D87533BFBE42C63FF2ABC77A34C79DB55A99171BBCB72C842A6530AF2F753F0C34AC63",
  "2F9F1E7949F0BF6C67665B27722A8857D626B6FF1A136D923A39F4069B7477FF946E5247A6627791D49B59ED",
  "C9E2525A860E6E9828D18F64A9F17222E8166A02453859BBDA0B8186D8C9928BB571E4146401D7430E225904",
  "673AD21CCAC54C146C248A1DD69AB6491E901D6D71B152155BE97DE057F3916A3F1B4273308C29B2F4D96971",
  "67B90681B1583ED930A71E990467DEA368134BECEEBD597F9BEC922E816F1B0570D728F4AE0464C1F797657F",
  "87A4E52DCDCAEB9272662EA66D7C6CD8781B31AF555AD93F5F65E75816CB8DC306BB67E592B5261BACA7C509",
  "629EA2AF8ABB80CBA89EE535B76DFD9CCBBE3BF48F2BC8AA34B26E1103291053F5CB8DE3A45AFA5A76DF8B21",
  "22ED2C82FBCF2259290D41A14F86B12F35F5D49762B34CFF13EE7E42EDEC70201D7F37C33316288FA3078E36",
  "E58108865C3CFE263D563692043DECC62F3426F86061285B7B1B336F56FF41BB65E9CD6D9B92FD90F864AA1C",
  "923CB8C755F5CDE1770D862595427149D7721AAAB5D194AEA9ACDECA15BE43CBA6A62B5A33909E9FC4DA1C58",
  "14FBD7CD6A2FA572E318B42C6C319140B86E66392580A11A2B431F44C1F9270E4F7B2490F3B325A9977A71A5",
  "75915636635B9969DBD6D220B24C3D99CEBBBD834B88222BD08C3ABE124E80"]

/-- Entry 0 as a `KatEntry` (`fpC` computed outside Lean). -/
def kat0 : KatEntry := ⟨0, kat0Msg, kat0Pk, kat0Sk, kat0Sm, 302752215737076496⟩

-- entry 0: every check of `EntryOk`
/-- info: true -/
#guard_msgs in
#eval entryOkB kat0

-- entry 0: HashToPoint equals the value `wC0` (Python `hashlib`)
/-- info: true -/
#guard_msgs in
#eval ((decodeSm round3 (hexL kat0Sm)).bind fun x => hashToPoint 512 (x.1 ++ x.2.1)).map
  (·.map Int.ofNat) = some wC0

/-- Entry 70 of `falcon512-KAT.rsp`: salt and message (bytes 2 to 41 + mlen of `sm`). -/
def kat70SaltMsg : String := String.join [
  "EC14011A2E55345B10861679D7746CBFBB1C12583E3303BFBDBBA2FEAF805C123A3B19C23F5D9F1095451139",
  "4B9D10E1BA162861802A717E24EE42A346C9ED280C88E267A41EC09D6D73B6076E7E30257BF265B71A0B6E0C",
  "F408F02BA9078811BE94D0F38559E9985463FC9671D182286CC4F18CABCAEE1A3E5ABDBC384FB27911168B54",
  "A387171C0524489FDF512E4D8D2F65050CFE7405D8DF63A79C6E42A76F4538907EFF4DC5870095241523F56F",
  "E8E389EBF1A1CC47DDB9F0188513D5259BE257BDA5BE7381F22392CDC2406E0F2448A80F3824F2670F61920C",
  "667499DE899F0F6B397381A2DE66255E061AB92CD864DE75C9DB7CBAB9FE76AC38E0AB3389530B4004055268",
  "B289B40D79B32E5EBCC74353510BD1627E2D5DD0BE7D3DFD04138F6E3EE7526133DC70490612EAA5024BE6FB",
  "EFAB24E1E83D8941A113D8B871F3DBC3011869174888CB7A265D7DE9AB99B999C19AF9B442EBDC904FEDAB52",
  "CF40B787AAB35626417C5291F2EB892F43E698A8C65CBB6442A4832F33920FB2DBFC50B8E996FB227F2FF294",
  "C385A330957D2FADA9F86839235EA79ECDE6D9D94FBE7C79A38D40B9A8F241F53B921107FF1C72624C9600EC",
  "04DFA1160F1FA9E5D986A5A363E9CE8627276DA73F5DB47E4B90328884CFE93194CFFA6FA680F77886E4A7A0",
  "FDAF13A7DDFF6984B8855E1F58235BABFD5106338FE2B075D4F10A9FB3D3C5F829B7C61B02B34E9BDE6E62CB",
  "CC3AC9F467A6CA170EB43E632EBDBF6847F781E2469B4740FDB83DA34CE34A286E3B363A72CBB13EB66CE1DE",
  "35D8FD77DBEDBF45C44DCD16E6B58A1699694D9006947C8C20810E85E3EBF8FB2C68B967743642D86556AB69",
  "58E545AB83EC24B96F2B4BB99CC8890C3C1E0FECCE26CE09B6D99000694F870AF9F642374FF0BBF61EFC7CD5",
  "AAF5667FC3FE5745DFAF7F13FED70FE070EA4C09CB1A92D8B7F0DFD4B4A4B7DCF4CA6A97043BCEF6346F1570",
  "F37B0EB48DB8D15C8A82ED69B0C7833D6C830414C111C987471E84D2CEB5BD973DCA34ACD3A65D7B1A502368",
  "941935435B78B8F2B74C2BEF127D96651247BDBE68EB7E466B9EA2A64A13C375103D7C8F7D30A13CBE184BD1",
  "EBB19F3274E645F5C7B82EFDF09233D8AD146DC0715266963FD3CCE6F8CDEC20743BF1B7F57C101AC24C64D5",
  "68923203E1A6AF03A700F5A401EC4572BBA528E284C151F1D108F7563858011FAB32B3776CF2B910D7B21180",
  "DBE75742032791018258F4D1407C9A213755C5C91205352DF919B6F14BE056243DF6AC2909E52C9A79F69174",
  "40667719185F1C5F1AAF40D873BA22956FA0BBAD9C35360853333A10A0841D9D2E758A0B1BC187F6BBD31C41",
  "B74F9EEEF1F7A28BDB7AC3D52FDC6FCB3EF0383A06A61188548963E552716D2BFBD6C2DCDE496D06615E86A5",
  "CDB76A03BCA2822ABA85EC6807EBB6918AD2948D193CCF74F4BDAF7090CD4294C1785DCEDB6B55886A848284",
  "A6A4A88A496800053E84A9F2DBF6B334AACE11A5A540626716302E259A64C6316ED543806B3BBFE37563897E",
  "83BBEFA570312DF908C1786DF0FCF55069EDC336501A5AE9D4BF212D56A9CEE811038656912238AE284575EF",
  "8DE1285B763AE54ADF44F91B6DD9E309B7A7A0AB71EC2E4611831B3CE1C9DC85CF907B52DF7406B06367E7A4",
  "3DECE72DCCC57D268820EA021C27056E3C6B50E7BA7A59B53539A6B7B06B35051E3151C23F3BD3C889B25D0E",
  "CE1FD0DF1AEDF657FBB096CA1C861ACB0158501EA1AEFBF6DAD11BDC325AC1CED3739A40B7A83458EF4F3453",
  "C0F6EABC1A48037809A90480DF9DC4FF07DADDC58DF2733D49A4FA53C2A41E55A4A0167C6D33BA6E752AED3A",
  "125DFD6A0322CD235254505D7B3CED7A0DEE7EB662ACFD30F8B79D1A872998CBCF15CD86E26809E0D2DA0324",
  "DDC90FD12CAF9D8E4EDA437FE4E658D47D67C95927C4B5DEE965B940CE93E6743917296E10820A7101F8F633",
  "C93069E8B569F4625AFD4EC61BFE4549FDD06C2290A91AC0FB40CB1F55DC8BC1FE695C73AF603840AC0351F5",
  "256E00555C984E79A09E58C566D1A117B7E569BEB5850FB491FD9B982442B55BDF53832AA65180DCDDC2F768",
  "B1A1361994DE8C25F3608EC853D5982E0AFD1F9FA70170FC3589DDAF958DD840B4B502F8E2697D01AD7AC223",
  "3F6A16D540EF8D232887D2B4FA727AE2F038A69AF3DAE69EDA8EF6BF1E0B67D811160B75231543EC5A4D0778",
  "B7B42FC1DD6732385AA4400450B3CAEEFDFFCF147635CFA4AAA53DE4EE3035BC40CE8670016384BB877A86A1",
  "5B59F3DF0C5D624D3D2B23EC46913618C745330A96C715C6F0BD096487E89B917384CC30B3D20A332F1B4056",
  "462227E98AF9874FF1D18DF2A6BF84AE822EE737F9E34EE8C69F23EEB9BF38ED056F499545F405759355C104",
  "284A6D08A9EFAD8FE28288B2084336A6479A6D42404F3E6FF3AD1DFC63C8AAE971AF11F2699F32F57AD29188",
  "492CE07BC1A271035B4D13A686EFDE5572353283A0F3138F6DC05CC35E5E5057C5C8B9E12B0164C0915ADEDF",
  "40A6E23848FA59ADC0E65BDD2120486942F232315FC94B4676751A35AAED2828889864C4CB7DD95A662A4757",
  "33C2CA8F6997A9C822C6C8B9DC95A8B4C367E613E97D3EC6D6DDC2F81022EC21B3A93244E3BC8C2737A7724A",
  "3CBD480B26819EEB2676FD383601D79FA266ED3F9BAC2A98FF0109AD7E43E33E108D88C09BA82AFCCCFE98F5",
  "0F789109D99DCD0A2C61947544F3666EDC621B5D5ECB7088B2430A611BEA52BE7F5EDFC6E2649F5E81F6DF72",
  "FA9A748BFF06AF766A60D2B751B23A8AA95CBF733359F7C0CD19B1482A6E6572D1570349C688D78CF8B8C7DD",
  "37576DC47A193A2C2797D0AF7504DEE303823A8B77204AE7B6E91D431979798A7EDF435056251D0E3F26B2CA",
  "16BFE3422CEA0398D30F0A0DC06DC8A93D27D13650E5BFB6BA04C93FAF0D7D06F99FE4F1F52A059FBE808179",
  "515FDA48ECA714F0947FE9A98F02D66FB0D80952411CDFCEAEF6ABA16D92B8F1B82DB151D7DCD7FB7781EC55",
  "F4A86C86011FBB9C5570EE76897E7803036E2FE3CDC2D5EA7A613897F3C69A6EA734E3811BFD15E90D7256A0",
  "C0C88CEB54EC6AAC151B435CD2A870E4A02087C2B847C75B00B44BB3CA6D4404C3052BD308B8D5F595277592",
  "D26F6D5A2193CD4D650BF931FEFB9DEEE61032B29EC0412F38E1CBE025B2891C59574C1450D9E3D8EF27940E",
  "F712143F06F38DDB86341A7FC781E0FA8971DAD13AA7E93F1858C70A71A40164211EA9F6A41AE90D19032C2E",
  "A52C23375CE3C4E59599ECD6855213AEA83F8DFC5CC70F58A62E4DCA17C09705C0C099B29056592986C03CF5",
  "D67074735F2BEA"]

-- entry 70: HashToPoint equals the value `wC70` (Python `hashlib`)
/-- info: true -/
#guard_msgs in
#eval (hashToPoint 512 (hexL kat70SaltMsg)).map (·.map Int.ofNat) = some wC70

-- the correctness theorems of `Codec` and `Verify` use only the standard axioms
/--
info: 'FalconPrecision.Exec.Codec.decodePk_encodePk' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodePk_encodePk
/--
info: 'FalconPrecision.Exec.Codec.encodePk_of_decodePk' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodePk_of_decodePk
/--
info: 'FalconPrecision.Exec.Codec.decodeSk_encodeSk' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeSk_encodeSk
/--
info: 'FalconPrecision.Exec.Codec.encodeSk_of_decodeSk' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeSk_of_decodeSk
/--
info: 'FalconPrecision.Exec.Codec.decompress_compress' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decompress_compress
/--
info: 'FalconPrecision.Exec.Codec.compress_of_decompress' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms compress_of_decompress
/--
info: 'FalconPrecision.Exec.Codec.decodeSig_encodeSig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeSig_encodeSig
/--
info: 'FalconPrecision.Exec.Codec.encodeSig_of_decodeSig' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeSig_of_decodeSig
/--
info: 'FalconPrecision.Exec.Codec.decodeSm_encodeSm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeSm_encodeSm
/--
info: 'FalconPrecision.Exec.Codec.encodeSm_of_decodeSm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms encodeSm_of_decodeSm
/--
info: 'FalconPrecision.Exec.Codec.decodePk_round3' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodePk_round3
/--
info: 'FalconPrecision.Exec.Codec.decodeSk_round3' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decodeSk_round3
/--
info: 'FalconPrecision.Exec.Codec.hashToPointL_mono' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hashToPointL_mono
/--
info: 'FalconPrecision.Exec.Codec.hashToPoint_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hashToPoint_spec
/--
info: 'FalconPrecision.Exec.Codec.verifyCore_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms verifyCore_iff

-- `entryOk_of`, `entriesOk_of` (`CodecKat`) use only the standard axioms
/--
info: 'FalconPrecision.Exec.Codec.entryOk_of' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms entryOk_of
/--
info: 'FalconPrecision.Exec.Codec.entriesOk_of' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms entriesOk_of
