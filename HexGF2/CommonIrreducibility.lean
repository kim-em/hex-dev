import HexGF2.RabinSoundness

/-!
Project-side irreducibility witnesses for committed packed `GF(2)` moduli.

The witnesses are produced by the Rabin certificate checker introduced in
`HexGF2/Irreducibility.lean` and bridged to `GF2Poly.Irreducible` through
`checkIrreducibilityCertificate_imp_irreducible`. Small witnesses can be
checked directly by `decide`; the larger GHASH witness stores quotient
certificates for each squaring step so kernel checking avoids repeated
degree-128 long division.
-/
namespace Hex
namespace GF2Poly

/-- The AES Rijndael modulus over `GF(2)`: `X^8 + X^4 + X^3 + X + 1`. -/
private def aesModulus : GF2Poly := ofUInt64Monic 0x1B 8

/-- Rabin certificate for the AES modulus. The pow chain stores
`X^(2^k) mod aesModulus` for `k = 0..8`; the single Bezout witness covers
the unique maximal proper divisor `d = 4` of `n = 8`.

Both the pow chain and the Bezout witness data are produced from the
executable `xpow2kMod` and `xgcd` so the certificate doubles as a
mechanical recipe. The chain is given as an explicit array literal so
kernel reduction (used by `decide` below) can normalize each entry
without going through the well-founded `Array.map`. -/
private def aesCert : IrreducibilityCertificate :=
  { n := 8
    powChain :=
      #[xpow2kMod aesModulus 0, xpow2kMod aesModulus 1, xpow2kMod aesModulus 2,
        xpow2kMod aesModulus 3, xpow2kMod aesModulus 4, xpow2kMod aesModulus 5,
        xpow2kMod aesModulus 6, xpow2kMod aesModulus 7, xpow2kMod aesModulus 8]
    bezout :=
      let diff := frobeniusDiffMod aesModulus 4
      let xg := xgcd aesModulus diff
      #[{ left := xg.left, right := xg.right }] }

set_option maxRecDepth 4096 in
private theorem aesCert_check :
    checkIrreducibilityCertificate aesModulus aesCert = true := by
  decide

/-- The AES Rijndael modulus `X^8 + X^4 + X^3 + X + 1` is irreducible over
`GF(2)`. -/
theorem aes_modulus_irreducible :
    Irreducible (ofUInt64Monic 0x1B 8) :=
  checkIrreducibilityCertificate_imp_irreducible aesModulus aesCert aesCert_check

/-- The degree-4 fixture modulus over `GF(2)`: `X^4 + X + 1`. -/
private def gf16Modulus : GF2Poly := ofUInt64Monic 0x3 4

/-- Rabin certificate for the degree-4 fixture modulus. The unique maximal
proper divisor of `4` is `2`, so the certificate has one Bezout leg. -/
private def gf16Cert : IrreducibilityCertificate :=
  { n := 4
    powChain :=
      #[xpow2kMod gf16Modulus 0, xpow2kMod gf16Modulus 1,
        xpow2kMod gf16Modulus 2, xpow2kMod gf16Modulus 3,
        xpow2kMod gf16Modulus 4]
    bezout :=
      let diff := frobeniusDiffMod gf16Modulus 2
      let xg := xgcd gf16Modulus diff
      #[{ left := xg.left, right := xg.right }] }

private theorem gf16Cert_check :
    checkIrreducibilityCertificate gf16Modulus gf16Cert = true := by
  decide

/-- The degree-4 fixture modulus `X^4 + X + 1` is irreducible over `GF(2)`. -/
theorem gf16_modulus_irreducible :
    Irreducible (ofUInt64Monic 0x3 4) :=
  checkIrreducibilityCertificate_imp_irreducible
    gf16Modulus gf16Cert gf16Cert_check

/-- The degree-16 fixture modulus over `GF(2)`: `X^16 + X^12 + X^3 + X + 1`. -/
private def gf65kModulus : GF2Poly := ofUInt64Monic 0x100B 16

/-- Rabin certificate for the degree-16 fixture modulus. The unique maximal
proper divisor of `16` is `8`, so the certificate has one Bezout leg. -/
private def gf65kCert : IrreducibilityCertificate :=
  { n := 16
    powChain :=
      #[xpow2kMod gf65kModulus 0, xpow2kMod gf65kModulus 1,
        xpow2kMod gf65kModulus 2, xpow2kMod gf65kModulus 3,
        xpow2kMod gf65kModulus 4, xpow2kMod gf65kModulus 5,
        xpow2kMod gf65kModulus 6, xpow2kMod gf65kModulus 7,
        xpow2kMod gf65kModulus 8, xpow2kMod gf65kModulus 9,
        xpow2kMod gf65kModulus 10, xpow2kMod gf65kModulus 11,
        xpow2kMod gf65kModulus 12, xpow2kMod gf65kModulus 13,
        xpow2kMod gf65kModulus 14, xpow2kMod gf65kModulus 15,
        xpow2kMod gf65kModulus 16]
    bezout :=
      let diff := frobeniusDiffMod gf65kModulus 8
      let xg := xgcd gf65kModulus diff
      #[{ left := xg.left, right := xg.right }] }

set_option maxRecDepth 4096 in
private theorem gf65kCert_check :
    checkIrreducibilityCertificate gf65kModulus gf65kCert = true := by
  decide

/-- The degree-16 fixture modulus `X^16 + X^12 + X^3 + X + 1` is
irreducible over `GF(2)`. -/
theorem gf65k_modulus_irreducible :
    Irreducible (ofUInt64Monic 0x100B 16) :=
  checkIrreducibilityCertificate_imp_irreducible
    gf65kModulus gf65kCert gf65kCert_check

/-- The GHASH degree-128 modulus: `X^128 + X^7 + X^2 + X + 1`. -/
private def ghashModulus : GF2Poly :=
  ofWords #[0x87, 0, 1]

/- Rabin certificate for the GHASH degree-128 modulus. The pow chain stores
precomputed `X^(2^k) mod ghashModulus` entries, avoiding a quadratic
certificate recomputation inside the kernel. -/
private def ghashCert : IrreducibilityCertificate :=
  { n := 128
    powChain :=
      #[ofWords #[0x2],
        ofWords #[0x4],
        ofWords #[0x10],
        ofWords #[0x100],
        ofWords #[0x10000],
        ofWords #[0x100000000],
        ofWords #[0x0, 0x1],
        ofWords #[0x87],
        ofWords #[0x4015],
        ofWords #[0x10000111],
        ofWords #[0x100000000010101],
        ofWords #[0x100010001, 0x1000000000000],
        ofWords #[0x100000001, 0x8700000001],
        ofWords #[0x86, 0x21caea],
        ofWords #[0x21cae93f7cfc8],
        ofWords #[0x4105551550555040, 0x401504454],
        ofWords #[0x118fe6196978ef70, 0x1001001111110961],
        ofWords #[0x93c692c775187987, 0x860140d2541486c6],
        ofWords #[0xea618e11df04ea1e, 0x8b69509b312d6501],
        ofWords #[0xcad0352d30b311b4, 0xb715594eb7756558],
        ofWords #[0x54e1a6f865fe82b9, 0x1afdeffd35e5fde],
        ofWords #[0x218289f09c0659ed, 0x11b4a30358935542],
        ofWords #[0x97b14587eebe264d, 0x83a513579eda5793],
        ofWords #[0x38d15180f9de45ad, 0x83ad91f69582bddf],
        ofWords #[0x1a97936b620f481d, 0xc7f8a41756ad614d],
        ofWords #[0xe94bf5687ccf4c39, 0xbb844bf6957599a6],
        ofWords #[0x5aadb3837634c244, 0x2c3bd83d0661350d],
        ofWords #[0x1f726995c3f33829, 0x24f6fc2353c7f232],
        ofWords #[0xa5b7efc52c5e9c53, 0x150e344316f35f82],
        ofWords #[0x891738c79d5ad319, 0xcbe66ebbc72d228a],
        ofWords #[0xfbb824714f38f6c2, 0xd331a77342cf2867],
        ofWords #[0x62609e6968de22b0, 0x60dcdee4d2f1fc92],
        ofWords #[0x21777af80695052a, 0x782d0a995dd3b018],
        ofWords #[0xde0a74a95b11a7b2, 0xcec3202236b9330f],
        ofWords #[0x800a7b44dd8e7a70, 0xcad1b2dd09125a5f],
        ofWords #[0x7016c540c190dd74, 0xd3f537e04c700e27],
        ofWords #[0x9bbaa007aff17a4, 0x20b022e1c1d1bc08],
        ofWords #[0xa5ea62f173a564de, 0x1c621e475a73acae],
        ofWords #[0xc1d3ada9e183a6f8, 0xeaab3a58b8a02fe2],
        ofWords #[0x2ee29c077314ee0d, 0xdffeae5cfc8592a2],
        ofWords #[0x1794c9c6116bca12, 0x1854548bb6f4de8e],
        ofWords #[0x5046371c4cc9eaa8, 0xa7ddbe68af10b36c],
        ofWords #[0xe77bd7620dd51099, 0xc7c20e0075b34cb3],
        ofWords #[0xe385088258930c85, 0xeed7a7597ab9140e],
        ofWords #[0xd9bf3b428f207eec, 0xd3807dd9d6a39649],
        ofWords #[0x7d1adaba58301148, 0x64fb855fc75b066a],
        ofWords #[0xaba3d15b0b675aaa, 0x710a093e99bb9946],
        ofWords #[0x66216c6f770b3b1e, 0xafc267d97044a1c8],
        ofWords #[0xfe1d7816d9eb81fd, 0xe316b61772920218],
        ofWords #[0xb87c1159421de6c0, 0xfbcf8c1e442c8cf5],
        ofWords #[0x687634c0bd8f66a6, 0x4d328e5ae8b1bde5],
        ofWords #[0xc8b21bf16608e4db, 0x4d758c29eeb484f7],
        ofWords #[0x939b53119c4b7496, 0x97da6d2e8f7686d],
        ofWords #[0xccbb31a458da0423, 0x60488351c7403436],
        ofWords #[0xaba321469362905f, 0x3c5814a4c792b3be],
        ofWords #[0xfbcf513b18b860f7, 0xf6fd92c58b52c44d],
        ofWords #[0xe213b075ac781973, 0x740252435434bd93],
        ofWords #[0xbb228613735755a8, 0xb7740311b0146782],
        ofWords #[0x4e059e6f77db9735, 0x14a4e774428f86a1],
        ofWords #[0x6728ba4f8b5ad996, 0x9f07d44ae7b5f72d],
        ofWords #[0xe68d429870a86444, 0x783e0e827a3c43a2],
        ofWords #[0xdddef6f866a8cb3a, 0x9ed6f0fd3b898356],
        ofWords #[0xac6ea52692d6e84f, 0x3dd46c137e3f5775],
        ofWords #[0x81aae137a9a1f2ac, 0xf64e2b2e01a18185],
        ofWords #[0x44e598a795a299f6, 0x61651fea6b5832b9],
        ofWords #[0xe4292c6d87e2a65, 0x7c9d30e6ed40cbc3],
        ofWords #[0xd47f657d9736a3bc, 0xc2c57e31da2ff653],
        ofWords #[0x55cb32146561a494, 0xe325ada8d4bf8eff],
        ofWords #[0x2b42640baf97546a, 0xbf884491f010fcf9],
        ofWords #[0x6f55c63e138b0f6a, 0x744ff1cc6c4147e9],
        ofWords #[0x44bd30ca7a959c35, 0xf72d4a117bba9cee],
        ofWords #[0xdd3c39ec2fcb97ec, 0x31f9706e56dcd7c9],
        ofWords #[0xf9104edc7cd7c419, 0xcafd0f1dee4b13f4],
        ofWords #[0x92f4024ed5a0366e, 0xc6b603373b7fff4c],
        ofWords #[0xe9408400053759bb, 0xfb4b047c029d81bd],
        ofWords #[0x22c6b03d1e52223, 0x5c12435b486ac2b0],
        ofWords #[0xcb1be4b63b5b3d, 0xdeb4814466d6d456],
        ofWords #[0x235138002e3dec62, 0x1c8f0314c1ca2c6a],
        ofWords #[0xb4fa968f61ea5bd8, 0xaa94fa2a07db8f59],
        ofWords #[0x1ec3403efa66966e, 0xbaed1a1f49ca7f89],
        ofWords #[0x42a87c2811ee47a, 0x79a3d532b4dca977],
        ofWords #[0x13581fc7a95df199, 0xca74daf67fe0c93b],
        ofWords #[0x8441bd78c444ed45, 0x92d3f21915a27173],
        ofWords #[0xdfc4ce06bfdce9ed, 0x52525b16c4db307],
        ofWords #[0xed08440dda5eba, 0x59a044e544805b99],
        ofWords #[0x7800914cc52e273b, 0xd6648859781bb4ef],
        ofWords #[0x9ad1a02c574e9631, 0x28266451a0c9c61d],
        ofWords #[0xcd3c813afb78aa38, 0x7c8647672078f3f4],
        ofWords #[0x494fdfab6df42306, 0x92c0cf343ae063ad],
        ofWords #[0xaca6f91a6abde544, 0x5574a07cca7cd737],
        ofWords #[0x879287c869f885c3, 0xbbada747894bc3dd],
        ofWords #[0xf50e0632f2a35f5b, 0x386db41096f62a8a],
        ofWords #[0x1843656b2ea8f397, 0xefdb454053648225],
        ofWords #[0xf1c52011971b40b3, 0x864204566cee644d],
        ofWords #[0x48e86e374780c55, 0x9f65220d0c78fc67],
        ofWords #[0x3caadfab02ea679d, 0x6c3124a15e087d32],
        ofWords #[0xdca8758ed620dd7b, 0x40e2dfc1450698ca],
        ofWords #[0x29e30e4d37b882a1, 0x217bea750913f0db],
        ofWords #[0x2452c0f06b2d5154, 0x18cc9c758f82f3a6],
        ofWords #[0xff4fc66638b9c77c, 0xa2f988953ebab6d6],
        ofWords #[0xb5cf3dbe01503955, 0x8b621a33b1f55be1],
        ofWords #[0x5bad32ffd131adf1, 0xa6403e49a18fdcec],
        ofWords #[0x8da7ee035acac1d8, 0xc7213453b5a00431],
        ofWords #[0x42908c445873de98, 0xfab85890c72cf5bd],
        ofWords #[0xaba9209e72802626, 0x18fb3bc896b15739],
        ofWords #[0x584b1b8ff9fdbe53, 0xe2ae4c18bc72d0b5],
        ofWords #[0x27fbbc64727757a3, 0xbf7fe7e158f5e6b6],
        ofWords #[0xc3ef36c9b75a0400, 0x74349545e390b89f],
        ofWords #[0xebaf56677af1691d, 0xb377c7044aeb289d],
        ofWords #[0x46b3da5829a07e0f, 0xdd4a597abff1c6d],
        ofWords #[0xfb31442bbbee4562, 0x390a7a5685925c88],
        ofWords #[0x8d931140ce80f4ca, 0xef0226d7d8c4f908],
        ofWords #[0x46bdf85b5f5764d5, 0xc77a431b17442dc2],
        ofWords #[0x9cb66967210ef752, 0xaaf58d8527dbb51e],
        ofWords #[0x12c3142c06e2acc1, 0xbea766c2fd57dce0],
        ofWords #[0x22ba9c65acbed68, 0x718b86e46755b667],
        ofWords #[0x77a7af910537779d, 0xeba2e73f8e06f46e],
        ofWords #[0xebbd0f52366f13ac, 0x9a6d9a22e2bcf10b],
        ofWords #[0xab2b66ce2a82776c, 0x30930047648b0f33],
        ofWords #[0x6015a35f3e3c8cc5, 0xdf6441de141c2ab5],
        ofWords #[0x8a24abe27faf17b9, 0x821656934ab0df9],
        ofWords #[0x8606bb0e28094f06, 0x6186189d20b81941],
        ofWords #[0x18637a81b61a75a5, 0x2cb2ca78e3a46e61],
        ofWords #[0xebacd53e52b72998, 0x34d34d3086928aea],
        ofWords #[0xdb490028e7b6cf92, 0xc71c71c308249e75],
        ofWords #[0x75d751453cf3b6ac, 0xebaebefbebaeb6db],
        ofWords #[0x8a28a28a1451455a, 0x9a69a69a61861861],
        ofWords #[0x6db6db6db6db6da4, 0x2492492492492492],
        ofWords #[0x2]]
    bezout :=
      #[{ left := ofWords #[0x214ec51f73e3547b, 0x34f319a5fb685836],
          right := ofWords #[0x41a8cafd2c95b018, 0x9e4af928ddbc838a] }] }

/-- Quotient witnesses for each GHASH pow-chain squaring step. Entry `k`
certifies `pow[k] * pow[k] = pow[k+1] + quotient[k] * ghashModulus`. -/
private def ghashPowQuotients : Array GF2Poly :=
      #[ofWords #[],
        ofWords #[],
        ofWords #[],
        ofWords #[],
        ofWords #[],
        ofWords #[],
        ofWords #[0x1],
        ofWords #[],
        ofWords #[],
        ofWords #[],
        ofWords #[],
        ofWords #[0x0, 0x100000000],
        ofWords #[0x1, 0x4015],
        ofWords #[0x40150445444],
        ofWords #[],
        ofWords #[0x1110010101110, 0x10],
        ofWords #[0x101010100411401, 0x100000100000101],
        ofWords #[0x1110011040145035, 0x4014000110005104],
        ofWords #[0x501045114110020, 0x4045144111004145],
        ofWords #[0x4515151114111163, 0x4515011111411054],
        ofWords #[0x5105115411555154, 0x1445551545555],
        ofWords #[0x1140410511111004, 0x101451044050005],
        ofWords #[0x4154514411154124, 0x4005441101051115],
        ofWords #[0x4111400445515174, 0x4005445141015514],
        ofWords #[0x1114445114011078, 0x5015554044100115],
        ofWords #[0x4111151141414437, 0x4545401010455514],
        ofWords #[0x14140105110053, 0x450054551400551],
        ofWords #[0x1105501555040506, 0x410551455500405],
        ofWords #[0x114550511554004, 0x111005405101005],
        ofWords #[0x501504510404406d, 0x5045541414544545],
        ofWords #[0x100450550440143c, 0x5105050144151505],
        ofWords #[0x510455015550410e, 0x1400515051545410],
        ofWords #[0x115151054500014a, 0x1540045100444141],
        ofWords #[0x51445410505007c, 0x5054500504000404],
        ofWords #[0x4101041144117c, 0x5044510145045151],
        ofWords #[0x105015000054043c, 0x5105551105155400],
        ofWords #[0x5001510145500042, 0x400450004045401],
        ofWords #[0x1144150544504454, 0x150140401541015],
        ofWords #[0x454044000455542f, 0x5444444505441140],
        ofWords #[0x555040114104442d, 0x5155555444541150],
        ofWords #[0x4514551051544054, 0x140111011104045],
        ofWords #[0x4455010045051473, 0x4415515145541440],
        ofWords #[0x151145051050452c, 0x5015500400540000],
        ofWords #[0x154445410110007f, 0x5454511544151141],
        ofWords #[0x5114440541141068, 0x5105400015515141],
        ofWords #[0x501511450014144e, 0x1410554540111155],
        ofWords #[0x414145454141101e, 0x1501004400410554],
        ofWords #[0x1500101044015063, 0x4455500414155141],
        ofWords #[0x150441040004016b, 0x5405011445140115],
        ofWords #[0x101004504050553a, 0x5545505540500154],
        ofWords #[0x5440450145515419, 0x1051050440541144],
        ofWords #[0x545445104010551d, 0x1051151140500441],
        ofWords #[0x5440551514401451, 0x41155144145104],
        ofWords #[0x501510000510051e, 0x1400104040051101],
        ofWords #[0x5015410445054556, 0x550114001104410],
        ofWords #[0x404511045010107a, 0x5514555141045011],
        ofWords #[0x111005104551410f, 0x1510000411041005],
        ofWords #[0x4500011014154027, 0x4515151000050101],
        ofWords #[0x1004405540144401, 0x110441054151510],
        ofWords #[0x5415451155150470, 0x4155001551101044],
        ofWords #[0x154405501005440e, 0x1540055400544004],
        ofWords #[0x545404140051135, 0x4154511455005551],
        ofWords #[0x1554055511151513, 0x551511014500105],
        ofWords #[0x144014001403a, 0x5514105404450454],
        ofWords #[0x144511400504454b, 0x1401141101555444],
        ofWords #[0x545110005045500f, 0x1550415105005414],
        ofWords #[0x514404555514112c, 0x5004501115540501],
        ofWords #[0x511045554054557e, 0x5405041144514440],
        ofWords #[0x5500010055505562, 0x4555404010104101],
        ofWords #[0x145010011015544b, 0x1510105555015050],
        ofWords #[0x154545444150547f, 0x5515045110440101],
        ofWords #[0x1114515051155043, 0x501554115001454],
        ofWords #[0x5454104501055539, 0x5044555100550151],
        ofWords #[0x545155555551079, 0x5014451400050515],
        ofWords #[0x441514001457a, 0x5545104500101550],
        ofWords #[0x1040144450044508, 0x1150010410051145],
        ofWords #[0x141451145110113d, 0x5154451040011010],
        ofWords #[0x5001504404501444, 0x150405500050110],
        ofWords #[0x15514540551162, 0x4444411055440444],
        ofWords #[0x1041504415554062, 0x4544545101440155],
        ofWords #[0x451051504441151f, 0x1541440551110504],
        ofWords #[0x155554005041056c, 0x5044151051445514],
        ofWords #[0x111440415011524, 0x4104510555040141],
        ofWords #[0x1450105145050015, 0x11041104114501],
        ofWords #[0x1010400011454149, 0x1141440010105411],
        ofWords #[0x154001454510547c, 0x5114141040401141],
        ofWords #[0x4400504150140153, 0x440041414101101],
        ofWords #[0x40015405505551a, 0x1550401410151415],
        ofWords #[0x544540014054470, 0x4104500050550510],
        ofWords #[0x504415505115051d, 0x1111151044001550],
        ofWords #[0x4041104550055172, 0x4545445144151015],
        ofWords #[0x4114551404444046, 0x540145145100100],
        ofWords #[0x110514104004043a, 0x5455514510111000],
        ofWords #[0x1450545414101070, 0x4014100400101114],
        ofWords #[0x50154055501434, 0x4155141104040051],
        ofWords #[0x115400401551050e, 0x1450050104104401],
        ofWords #[0x101100144140504c, 0x1000540451555001],
        ofWords #[0x41010555005147, 0x401154554441511],
        ofWords #[0x4055400455054414, 0x140505041501511],
        ofWords #[0x554454445145137, 0x4404554140404111],
        ofWords #[0x4501551111455420, 0x4045140401440505],
        ofWords #[0x4401405551505473, 0x4414100005541041],
        ofWords #[0x4511440000100528, 0x5015040105101105],
        ofWords #[0x501504505511457a, 0x5544454011404100],
        ofWords #[0x4114450111150541, 0x140554505455040],
        ofWords #[0x455015045100453a, 0x5404445410500140],
        ofWords #[0x1140551154144537, 0x4555155554155401],
        ofWords #[0x540541004540415f, 0x1510051041111011],
        ofWords #[0x1044544504404172, 0x4505151550150010],
        ofWords #[0x4445555501501451, 0x51511044114115],
        ofWords #[0x4011410411504042, 0x541004415441114],
        ofWords #[0x514050105541006b, 0x5455000404145115],
        ofWords #[0x11510100451502d, 0x5015154410050145],
        ofWords #[0x415514545110177, 0x4444551140514011],
        ofWords #[0x5551111551505423, 0x4554441514145004],
        ofWords #[0x141511114514141f, 0x1501404540145410],
        ofWords #[0x405400145510147f, 0x5445440454150555],
        ofWords #[0x5404455055010064, 0x4144145141440404],
        ofWords #[0x1410404500550507, 0x500410500001015],
        ofWords #[0x110015004444538, 0x5155141010015154],
        ofWords #[0x510444500515541, 0x40040114111441],
        ofWords #[0x40045400141100b, 0x1401401401404151],
        ofWords #[0x5405441014541403, 0x450450450441540],
        ofWords #[0x4014410440445446, 0x510510510510500],
        ofWords #[0x40041041541538, 0x5015015015015005],
        ofWords #[0x544544544514516e, 0x5445445445545545],
        ofWords #[0x1401401401401420, 0x4144144144144144],
        ofWords #[0x4104104104104106, 0x410410410410410]]

private def checkPowChainQuotientWitnesses (f : GF2Poly)
    (cert : IrreducibilityCertificate) (quotients : Array GF2Poly) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    quotients.size == cert.n &&
    (cert.powChain[0]? == some (monomial 1 % f)) &&
    (List.range cert.n).all fun k =>
      match cert.powChain[k]?, cert.powChain[k + 1]?, quotients[k]? with
      | some prev, some curr, some quot =>
          (curr.isZero || decide (curr.degree < f.degree)) &&
            (prev * prev == curr + quot * f)
      | _, _, _ => false

private theorem list_all_eq_true_of_mem {α : Type u} {xs : List α} {p : α → Bool}
    (hall : xs.all p = true) {x : α} (hx : x ∈ xs) : p x = true := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rcases hall with ⟨hy, hys⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hy
      · exact ih hys hx

private theorem checkPowChainLinear_of_quotientWitnesses
    {f : GF2Poly} {cert : IrreducibilityCertificate} {quotients : Array GF2Poly}
    (h : checkPowChainQuotientWitnesses f cert quotients = true) :
    checkPowChainLinear f cert = true := by
  unfold checkPowChainQuotientWitnesses at h
  unfold checkPowChainLinear
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hsize, _hquotSize⟩, hfirst⟩, hsteps⟩ := h
  refine ⟨⟨hsize, hfirst⟩, ?_⟩
  rw [List.all_eq_true]
  intro k hk
  have hstep := list_all_eq_true_of_mem hsteps hk
  cases hprev : cert.powChain[k]? with
  | none =>
      rw [hprev] at hstep
      exact False.elim (Bool.noConfusion hstep)
  | some prev =>
      cases hcurr : cert.powChain[k + 1]? with
      | none =>
          rw [hprev, hcurr] at hstep
          exact False.elim (Bool.noConfusion hstep)
      | some curr =>
          cases hquot : quotients[k]? with
          | none =>
              rw [hprev, hcurr, hquot] at hstep
              exact False.elim (Bool.noConfusion hstep)
          | some quot =>
              rw [hprev, hcurr, hquot] at hstep
              simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hstep
              obtain ⟨hred, hmulBeq⟩ := hstep
              have hmul : prev * prev = curr + quot * f := eq_of_beq hmulBeq
              have hsquare : sqMod f prev = curr := by
                unfold sqMod
                exact mod_eq_of_eq_add_mul_right hmul hred
              simp [hsquare]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8192 in
private theorem ghashPowQuotients_check :
    checkPowChainQuotientWitnesses ghashModulus ghashCert ghashPowQuotients = true := by
  decide

set_option maxRecDepth 8192 in
private theorem ghashCert_check :
    checkIrreducibilityCertificateLinear ghashModulus ghashCert = true := by
  unfold checkIrreducibilityCertificateLinear
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · decide
  · decide
  · exact checkPowChainLinear_of_quotientWitnesses ghashPowQuotients_check
  · decide
  · decide

/-- The GHASH degree-128 modulus `X^128 + X^7 + X^2 + X + 1` is
irreducible over `GF(2)`. -/
theorem gf2nPoly_modulus_irreducible :
    Irreducible (ofWords #[0x87, 0, 1]) :=
  checkIrreducibilityCertificateLinear_imp_irreducible
    ghashModulus ghashCert ghashCert_check

end GF2Poly
end Hex
