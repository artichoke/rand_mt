// src/mt19937.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

use std::cmp::{max, Ordering};
use std::default::Default;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::num::Wrapping;

use rand::{Rand, Rng, SeedableRng};

const N: usize = 624;
const M: usize = 397;
const ONE: Wrapping<u32> = Wrapping(1);
const MATRIX_A: Wrapping<u32> = Wrapping(0x9908b0df);
const UPPER_MASK: Wrapping<u32> = Wrapping(0x80000000);
const LOWER_MASK: Wrapping<u32> = Wrapping(0x7fffffff);

/// The 32-bit flavor of the Mersenne Twister pseudorandom number
/// generator.
#[derive(Copy)]
pub struct MT19937 {
    idx: usize,
    state: [Wrapping<u32>; N],
}

const UNINITIALIZED: MT19937 = MT19937 {
    idx: 0,
    state: [Wrapping(0); N],
};

impl SeedableRng<u32> for MT19937 {
    #[inline]
    fn from_seed(seed: u32) -> MT19937 {
        let mut mt = UNINITIALIZED;
        mt.reseed(seed);
        mt
    }

    fn reseed(&mut self, seed: u32) {
        self.idx = N;
        self.state[0] = Wrapping(seed);
        for i in 1..N {
            self.state[i] = Wrapping(1812433253) * (self.state[i - 1] ^ (self.state[i - 1] >> 30))
                + Wrapping(i as u32);
        }
    }
}

impl<'a> SeedableRng<&'a [u32]> for MT19937 {
    #[inline]
    fn from_seed(seed: &[u32]) -> MT19937 {
        let mut mt = UNINITIALIZED;
        mt.reseed(seed);
        mt
    }

    fn reseed(&mut self, key: &[u32]) {
        self.reseed(19650218u32);
        let mut i = 1;
        let mut j = 0;
        for _ in 0..max(N, key.len()) {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 30)) * Wrapping(1664525)))
                + Wrapping(key[j])
                + Wrapping(j as u32);
            i += 1;
            if i >= N {
                self.state[0] = self.state[N - 1];
                i = 1;
            }
            j += 1;
            if j >= key.len() {
                j = 0;
            }
        }
        for _ in 0..N - 1 {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 30)) * Wrapping(1566083941)))
                - Wrapping(i as u32);
            i += 1;
            if i >= N {
                self.state[0] = self.state[N - 1];
                i = 1;
            }
        }
        self.state[0] = Wrapping(1 << 31);
    }
}

impl SeedableRng<u64> for MT19937 {
    #[inline]
    fn from_seed(seed: u64) -> MT19937 {
        let mut mt = UNINITIALIZED;
        mt.reseed(seed);
        mt
    }

    #[inline]
    fn reseed(&mut self, seed: u64) {
        let seeds = [seed as u32, (seed >> 32) as u32];
        self.reseed(&seeds[..]);
    }
}

impl Rng for MT19937 {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        // Failing this check indicates that, somehow, the structure
        // was not initialized.
        debug_assert!(self.idx != 0);
        if self.idx >= N {
            self.fill_next_state();
        }
        let Wrapping(x) = self.state[self.idx];
        self.idx += 1;
        temper(x)
    }
}

impl MT19937 {
    /// Create a new Mersenne Twister random number generator using
    /// the default fixed seed.
    #[inline]
    pub fn new_unseeded() -> MT19937 {
        SeedableRng::from_seed(5489u32)
    }

    fn fill_next_state(&mut self) {
        for i in 0..N - M {
            let x = (self.state[i] & UPPER_MASK) | (self.state[i + 1] & LOWER_MASK);
            self.state[i] = self.state[i + M] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        }
        for i in N - M..N - 1 {
            let x = (self.state[i] & UPPER_MASK) | (self.state[i + 1] & LOWER_MASK);
            self.state[i] = self.state[i + M - N] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        }
        let x = (self.state[N - 1] & UPPER_MASK) | (self.state[0] & LOWER_MASK);
        self.state[N - 1] = self.state[M - 1] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        self.idx = 0;
    }

    /// Recover the internal state of a Mersenne Twister instance
    /// from 624 consecutive outputs of the algorithm.
    ///
    /// The returned `MT19937` is guaranteed to identically reproduce
    /// subsequent outputs of the RNG that was sampled.
    ///
    /// Panics if the length of the slice is not exactly 624.
    pub fn recover(samples: &[u32]) -> MT19937 {
        assert!(samples.len() == N);
        let mut mt = UNINITIALIZED;
        for (in_, out) in Iterator::zip(samples.iter(), mt.state.iter_mut()) {
            *out = Wrapping(untemper(*in_));
        }
        mt.idx = N;
        mt
    }
}

#[inline]
fn temper(mut x: u32) -> u32 {
    x ^= x >> 11;
    x ^= (x << 7) & 0x9d2c5680;
    x ^= (x << 15) & 0xefc60000;
    x ^= x >> 18;
    x
}

#[inline]
fn untemper(mut x: u32) -> u32 {
    // reverse "x ^=  x>>18;"
    x ^= x >> 18;

    // reverse "x ^= (x<<15) & 0xefc60000;"
    x ^= (x << 15) & 0x2fc60000;
    x ^= (x << 15) & 0xc0000000;

    // reverse "x ^= (x<< 7) & 0x9d2c5680;"
    x ^= (x << 7) & 0x00001680;
    x ^= (x << 7) & 0x000c4000;
    x ^= (x << 7) & 0x0d200000;
    x ^= (x << 7) & 0x90000000;

    // reverse "x ^=  x>>11;"
    x ^= x >> 11;
    x ^= x >> 22;

    x
}

impl Default for MT19937 {
    #[inline]
    fn default() -> MT19937 {
        MT19937::new_unseeded()
    }
}

impl Rand for MT19937 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Self {
        SeedableRng::from_seed(rng.gen::<u64>())
    }
}

#[test]
fn test_32bit_seeded() {
    let mt: MT19937 = SeedableRng::from_seed(0x12345678u32);
    for (&Wrapping(x), &y) in mt.state.iter().zip(STATE_SEEDED_BY_U32.iter()) {
        assert!(x == y);
    }
}

#[test]
fn test_32bit_slice_seeded() {
    let mt: MT19937 = SeedableRng::from_seed(&[0x123u32, 0x234u32, 0x345u32, 0x456u32][..]);
    for (&Wrapping(x), &y) in mt.state.iter().zip(STATE_SEEDED_BY_SLICE.iter()) {
        assert!(x == y);
    }
}

#[test]
fn test_32bit_output() {
    let mut mt: MT19937 = SeedableRng::from_seed(&[0x123u32, 0x234u32, 0x345u32, 0x456u32][..]);
    for x in TEST_OUTPUT.iter() {
        assert!(mt.next_u32() == *x);
    }
}

#[cfg(test)]
static STATE_SEEDED_BY_U32: [u32; N] = [
    305419896, 775181657, 499207455, 1600259134, 3349832671, 2158895569, 3851567941, 933167269,
    2845216289, 560713432, 2837590850, 1856731211, 4010544958, 3935610910, 4016625791, 3415983355,
    3013963240, 561813347, 3403724065, 2542053501, 4110119215, 3740807793, 1141434640, 666176716,
    4158339220, 1525097132, 2105164635, 3200105629, 119898583, 623462640, 4293015246, 4281226240,
    139575375, 2656314956, 1943329512, 3833597712, 471604643, 3060329588, 1563062452, 3909244048,
    2167605543, 621439170, 3833145012, 1015362910, 1202674754, 3932438940, 326377, 3567038236,
    2573315691, 3669950622, 3304735523, 4203256787, 4126656836, 443181112, 3611891278, 618660248,
    2556623152, 4274393843, 1222109418, 3410077682, 2539535185, 3375485692, 1670100441, 592926327,
    1073466419, 402905952, 160165154, 2047459501, 849940512, 1731493093, 1757891130, 3908492430,
    2303162601, 3679811584, 3523671161, 3169435245, 2821359895, 3082244758, 1217448114, 493615598,
    2715547958, 1418864085, 213082358, 1885529953, 410495284, 1093572057, 3732518542, 1653701368,
    654558613, 2890707234, 1558970874, 3892910946, 384153249, 3787732706, 2146373667, 836865993,
    510610349, 2669899938, 1419841410, 1164786194, 1924207843, 3996659599, 1785769634, 3596558774,
    3297061329, 2292769347, 3883732239, 2879754791, 4002117125, 2170078923, 3320250043, 1232795399,
    350202830, 2312242871, 1348895451, 544098933, 915340701, 929961062, 1579328180, 2075135712,
    1486047293, 224893989, 2641586195, 3853527088, 2171086747, 1819771098, 2836924901, 1293518754,
    2384314063, 2960325730, 2366435938, 3027304547, 2557480905, 792125084, 3825946642, 1657188412,
    3663670681, 1311402059, 2593177532, 3622458497, 3191531990, 1764537649, 2682924158, 4036356475,
    660493544, 905947161, 1132573551, 1530112249, 3751174764, 906706272, 2212992886, 244831579,
    1016193151, 2922023348, 108313448, 70293667, 2572186603, 35941514, 2251992336, 2940398265,
    1143058279, 3153185247, 1282861523, 3402211965, 2197064282, 1894493533, 977641970, 3334563617,
    342680338, 569915587, 245612697, 953933320, 2328420820, 3069616155, 396987275, 2254336390,
    1486777796, 3684875370, 820479775, 4169197294, 1391128885, 4197580345, 3797702552, 2190312414,
    2825503364, 3833427351, 4034369566, 1147242796, 3911136381, 1138304115, 273310648, 2529087575,
    622374729, 1871329678, 3779018029, 3388129769, 2616376342, 32958633, 2441821299, 1113477724,
    634733689, 4195861894, 3870825283, 1274544395, 4037854142, 2132041566, 3115087945, 2071501158,
    3866994035, 4079695361, 1644257692, 1326680260, 2152293261, 4028944192, 1615176005, 1470235819,
    537973226, 475991083, 2284835025, 191057690, 3308855326, 2122592590, 1437842441, 2210494471,
    3903981529, 1130808291, 1233992460, 2997699076, 2363114306, 920242469, 1284778367, 3407531421,
    3236867646, 1494508538, 2926167537, 1481581770, 3614910467, 3731540205, 3425346772, 2498435266,
    1044350128, 1843497569, 1437137106, 177739570, 1288235438, 136043008, 279380726, 3476279813,
    3238073174, 471342722, 2875563076, 3449953945, 2978774462, 4225447977, 4021396368, 514077950,
    2450970422, 2929310853, 1144824133, 1997866199, 2763747186, 2561009717, 2419789241, 3317857998,
    254983401, 2625386998, 3182588494, 2259010823, 1425631493, 2394264481, 1192917853, 1761273947,
    63690386, 188598955, 797145481, 967329056, 809592500, 3366967833, 936310616, 2859314895,
    862760185, 960528470, 3850021128, 1898485106, 4146233979, 699904629, 19727943, 2937092642,
    3116060608, 2330151595, 3309299407, 1682783135, 816977018, 2324520775, 145065055, 2948403618,
    2137429320, 173799414, 3719658296, 3660132978, 727081153, 1679980114, 858790637, 2833151408,
    4238258794, 3304428958, 1967131939, 1027236253, 1301317925, 3815137385, 3689071880, 590848398,
    4249467966, 1165945418, 1652659153, 4293501515, 3472723876, 3178958112, 1333879208, 2465069548,
    2418407974, 953480565, 1972598123, 988352021, 890162317, 3995675110, 3203143071, 2113965368,
    3931781573, 3673014887, 496055998, 130566209, 2792770545, 2465596204, 553967732, 3057034003,
    3259592709, 2350279087, 589318035, 453962066, 2700931246, 88801585, 4002525867, 3668927903,
    3151467492, 2373808407, 3885292451, 2292402043, 1241117977, 3345976277, 2075243212, 1164329280,
    1326090501, 1100428277, 656479398, 3164863713, 3711779315, 520385813, 2935844783, 3028002216,
    2685818746, 568835009, 4063124879, 4214150567, 827002656, 2274695437, 1269099353, 2842358567,
    1431550985, 4259412121, 397738036, 686877175, 2919399143, 287809230, 943711932, 47490467,
    905876935, 2550765564, 1846666928, 4233870928, 3780215611, 3135880853, 3210215953, 2841247230,
    995168748, 3607584669, 224807128, 608065211, 3961474123, 1579393517, 858402722, 1754300017,
    1237046200, 1903659654, 2063394765, 1147642119, 1631108842, 368842564, 3888419682, 2534674388,
    238929662, 1188000199, 2552552112, 3530656717, 2235525082, 2004783565, 3985224466, 2040447052,
    2930119929, 1067293600, 852953018, 3490617341, 889906898, 2861659255, 2917699783, 597527640,
    1403746392, 2625445310, 3530184910, 3608526724, 2948911335, 4273207550, 1479254647, 1549942837,
    3096128044, 3619439567, 3357732134, 3199426116, 1445046602, 1139666756, 3368965351, 655459235,
    651176959, 2141574220, 1696921875, 408872909, 974727829, 1774881662, 2248737233, 3293357302,
    1429680993, 283485849, 2867961111, 3858118660, 4199603071, 1472198057, 4039824646, 2066266552,
    2189707453, 3663195164, 3135619325, 2347146590, 3115733776, 3034671583, 530647799, 707298362,
    1716860586, 2626491968, 3093371860, 3239019321, 2263798190, 1445054121, 1564166678, 1034652642,
    1303913466, 348423896, 765119754, 2836611269, 3149139799, 2979105630, 2441361698, 1000123255,
    1087592139, 1146706315, 1928408908, 848486460, 4288058760, 658334900, 118034658, 1858772233,
    3476110856, 1861115704, 4220523615, 3108062767, 3968452261, 2218014563, 2313405483, 4092942100,
    2701634811, 1785168166, 1527043405, 1679938791, 1989285546, 3094443620, 3253358124, 3700490618,
    3041810349, 2929606908, 2217317416, 702017669, 3247182701, 1118538331, 3677208952, 603269758,
    3035181998, 643592405, 2360181507, 1553414752, 4203672385, 3647098119, 706447506, 2901476761,
    3260295975, 340216629, 2446527211, 293142768, 3972911284, 2061912376, 3331942019, 1071641223,
    2715152459, 3036536790, 3552429230, 1960456012, 2759843949, 1285027032, 3354049707, 2267699287,
    1129142425, 2115325449, 2808222522, 2894237483, 608071233, 627657402, 2661156728, 3534700345,
    445644282, 4086300603, 3316735410, 636793328, 173254092, 1867421593, 1045047574, 2866347469,
    3424185291, 2927300617, 3329243513, 1667168581, 2293874168, 29933511, 1430661801, 1008385647,
    260016883, 2941443848, 3595852572, 1172606054, 757040591, 2830406616, 894697776, 1192700447,
    1082109446, 2092067316, 4006276315, 1756826475, 1295596806, 3094271224, 1586090712, 1579504340,
    1038134593, 3475187166, 3442227051, 4293953091, 1568487804, 882283918, 1414791492, 1588948856,
    2391522813, 3418910428, 3313637181, 1433754553, 2808785372, 1863242971, 2327357000, 1339897721,
    155065504, 724757865, 369352119, 86927998, 4089410562, 933515186, 676836744, 829974775,
    124689091, 2664066112, 3348761180, 2347495630, 495398608, 101894757, 2558322991, 1582044696,
    310844213, 3075480386, 4025483930, 3108235704, 1274397374, 1684475576, 915984987, 2002432838,
    2074786915, 2816132875, 2333301231, 2872922596, 2773444642, 267204357, 3626722399, 274192051,
    3614605831, 2245882365, 72905477, 1301680228, 4189947717, 806672139, 2761604293, 3716414450,
];

#[cfg(test)]
static STATE_SEEDED_BY_SLICE: [u32; N] = [
    2147483648, 1827812183, 1371430253, 3559376401, 4152304030, 3484546413, 904688886, 2640105624,
    3033298696, 3386595201, 369478181, 2269089429, 618892536, 1404079710, 2891471128, 2871169702,
    1020385029, 3311824836, 923090660, 1921041923, 1544466474, 685797265, 2465597578, 2346973074,
    630894856, 665182002, 769175936, 3017123521, 3508859727, 1803296144, 2059566241, 4053644259,
    3993140148, 741891261, 54278865, 20043431, 2445648452, 1044381999, 1773042707, 2768959228,
    1818875112, 2035786986, 3458871676, 4190322778, 1552412821, 3743407409, 921020090, 3028219647,
    1811282874, 458436201, 2261805142, 3540504881, 55523394, 3406035835, 3643554219, 160478601,
    3131812209, 1750246847, 310524801, 538838761, 4097216171, 1424467795, 1736964303, 3924877158,
    4050066274, 1284818847, 997608279, 1743645731, 3861638089, 1979190831, 331968179, 67771207,
    937697508, 3340056593, 752755706, 1581536688, 2292813118, 822270257, 3518209714, 3540339067,
    1356302093, 564364160, 3439306709, 4156257291, 2902329296, 2676847202, 199377087, 2700614214,
    4256495779, 1042379751, 1902843850, 541663347, 1105719791, 2055488122, 1772382387, 1590461887,
    1096731286, 4039442187, 1175370089, 1659062698, 53134572, 2821322629, 3865246561, 1928684207,
    2238726924, 3291877865, 2486983120, 2591476417, 2633030347, 4263927136, 3370274455, 3018969306,
    3342536519, 1048809092, 3887576647, 1798999130, 1882276042, 2314104910, 3303817434, 2251178951,
    1354109516, 2944211425, 542518603, 3545156308, 292048272, 1667455762, 1824881537, 2291719689,
    2601744913, 1475382386, 2151236187, 3551355316, 207179492, 4025262836, 4201541508, 4185568575,
    1371095840, 2533214650, 750598898, 3336127010, 1112746635, 2168833184, 1866663264, 1008882524,
    705705152, 434584641, 3720585473, 1359539617, 1186019465, 2997504282, 3279906530, 4174236237,
    1111392757, 1874728325, 3994133610, 855552173, 1490712571, 770322226, 3509743848, 3097776221,
    1669989606, 2981948555, 3420675648, 763522569, 1854726402, 1446282084, 4210797998, 3497860296,
    1500567652, 4170419592, 375681337, 1685467682, 3252917671, 204735328, 725724149, 86204629,
    3407749819, 1497038849, 1240663743, 1497563373, 330463645, 678281313, 555587055, 3420977290,
    3864978040, 2598258963, 88433849, 706471606, 2204253466, 1207243547, 479433004, 2525229949,
    3011716495, 3622461821, 2931310287, 994916916, 3209595751, 3887340275, 1441571561, 2496624432,
    3592967859, 2170622192, 3964102663, 1750936864, 4286251765, 2410873793, 4056435468, 3778832465,
    3568403537, 3195560039, 2447945345, 2289664522, 3125246309, 3254932065, 3412281324, 1070323682,
    1454196965, 1242606593, 2025763526, 2480282382, 1785523412, 1678120983, 3466302448, 913688339,
    2335682621, 2870884017, 3943203012, 3376940353, 821708821, 5329814, 2050965739, 4012960695,
    4026282590, 848005093, 2090115245, 1732838459, 1701934203, 2618985574, 2392637351, 3610308264,
    1162509741, 3772926898, 4026399774, 2801305136, 2182020938, 2540720293, 4177612013, 3758227323,
    2141839466, 3457019126, 690868322, 598123635, 4220136616, 2063722767, 534543515, 3995640444,
    3697772838, 605496025, 194542699, 4283492525, 3414550867, 2944993929, 3138370086, 2273260021,
    1368435547, 328762456, 2810028600, 3571321502, 1782649452, 4008389438, 3374096016, 2070297302,
    3548106024, 406229528, 420474145, 1345435476, 1454548380, 2158312864, 1379619651, 1353546123,
    3811653577, 882683258, 2752377205, 3614226931, 1500298293, 2610950419, 1253921430, 2107280447,
    2276719522, 1296486334, 3787958895, 3076802280, 1113584194, 1511963190, 4162049235, 3993023547,
    3616161164, 1305747926, 3972166487, 1967370814, 920085398, 3066264196, 3270634177, 116308049,
    3500602755, 2095466291, 374997835, 4013819058, 294797265, 2531304952, 1915167960, 667114423,
    33740368, 2659595205, 1992038463, 1788663246, 1032288339, 2725176344, 965149701, 2340916620,
    2880875099, 90563045, 550093497, 2205859613, 4113574329, 2611773242, 6224964, 2216769577,
    2724275975, 1825208654, 1095989352, 1353654145, 4130469231, 2872700633, 3968090132, 3983530071,
    3891778552, 253511543, 3451123488, 1858275584, 2348219340, 4164791526, 1546492002, 2318605776,
    1965910834, 4016688232, 1661025458, 2551621891, 2559017942, 2999442539, 2626132036, 3855956683,
    889284004, 4228792998, 2508936804, 2464411834, 3126525029, 1845662917, 1099875911, 230942152,
    1316977638, 4287590380, 3960960001, 2035696777, 2084606597, 4185117397, 272555796, 1438814277,
    3792058704, 2373818687, 328461098, 1933025545, 478993165, 2186693443, 2504363491, 2844647904,
    4178236473, 174820621, 3894751753, 3928736686, 691843130, 3709350628, 2757608178, 1391782179,
    1043240547, 2220523142, 2016183159, 2906513762, 3465827756, 3911890461, 2425950392, 948237040,
    3362307558, 826526964, 1022776727, 1602110624, 495555482, 3374275041, 1251359676, 1255187341,
    2187964004, 2260892791, 2998084135, 1359605011, 1974780261, 150018524, 729982456, 538716187,
    2451949310, 1404163987, 323166556, 3575751708, 912151627, 1062492739, 136196234, 1525463811,
    3934317698, 4059639798, 1714397141, 3799270074, 3933323871, 1950899325, 2202877835, 512028145,
    121304123, 1747320652, 4025527049, 3203512622, 370863179, 1383153679, 338573713, 843668046,
    3786076594, 3761568863, 1943691400, 4239756727, 2866888284, 927687523, 2835168303, 3639022486,
    4177667412, 2454774443, 3330293413, 1073705099, 489962519, 2122918676, 3091912613, 2087072392,
    2474785306, 4196422017, 1950304138, 1417647053, 3170449575, 2871308877, 2834888397, 2515213887,
    706488188, 2765291661, 3342253292, 946613144, 2657539519, 1870033541, 2568978334, 2381242604,
    2390291123, 1426830313, 1033183417, 1865206616, 3909956281, 3229647106, 567876042, 2632601739,
    1787091399, 1136358267, 1707922556, 3600383805, 83493536, 3720481151, 1860566046, 1457764290,
    1087693608, 2574737982, 3472233887, 1946429651, 657205714, 1561347349, 3458704973, 658970395,
    2666292445, 4010435611, 2923502084, 2919668932, 1447403386, 272213229, 2379902797, 856095986,
    390957008, 316624381, 37938916, 1312588871, 3443811924, 3563720170, 681138701, 3713652810,
    1229426900, 45899309, 3319920329, 3184643346, 1733808374, 3218014532, 4131837143, 2708745467,
    1925606777, 1070300412, 1857066639, 231709688, 89357594, 2807557743, 4246955725, 2648639203,
    4014481964, 3609309784, 3413370774, 3362710738, 4117303240, 2975382313, 4244728709, 676814731,
    1401643182, 4193290992, 1880982784, 3412352641, 432923266, 3204217730, 3640767186, 2748687591,
    3238328348, 1816348975, 3454683239, 1788280760, 2390076397, 583783115, 749971462, 2070386333,
    3684914363, 2505473379, 3781484919, 3251603932, 1061410633, 2657465574, 1047386942, 598203491,
    3802852895, 3892183081, 650367471, 1888164348, 3790664944, 3285152048, 1772040010, 2779620173,
    262034140, 4011996451, 172805695, 3112617504, 3698026131, 2749738982, 1338645063, 2883589338,
    1171912066, 1463032348, 2303251030, 1690714656, 87045526, 3931593098, 1973669665, 2196833368,
    3131780013, 2099423072, 3143196216, 2732157577, 3060002362, 3279855788, 2424755944, 3186596011,
    892164315, 1948474334, 1752877034, 3954052922, 2895910728, 2605843797, 41504255, 2282306723,
    2818684947, 2301112141, 125160123, 16831279, 2001639563, 2988100720, 2804013521, 1917204704,
    2217119131, 747297802, 57526359, 1150692435, 1127421285, 1638007393, 2357393576, 1363062508,
    112227006, 1305326547, 2699963315, 3027707384, 2567899981, 539524824, 1322391149, 4115045373,
    2610809222, 1511354791, 1747171732, 2430429081, 2427698197, 668479568, 1616806017, 77518867,
];

#[cfg(test)]
static TEST_OUTPUT: [u32; 1000] = [
    1067595299, 955945823, 477289528, 4107218783, 4228976476, 3344332714, 3355579695, 227628506,
    810200273, 2591290167, 2560260675, 3242736208, 646746669, 1479517882, 4245472273, 1143372638,
    3863670494, 3221021970, 1773610557, 1138697238, 1421897700, 1269916527, 2859934041, 1764463362,
    3874892047, 3965319921, 72549643, 2383988930, 2600218693, 3237492380, 2792901476, 725331109,
    605841842, 271258942, 715137098, 3297999536, 1322965544, 4229579109, 1395091102, 3735697720,
    2101727825, 3730287744, 2950434330, 1661921839, 2895579582, 2370511479, 1004092106, 2247096681,
    2111242379, 3237345263, 4082424759, 219785033, 2454039889, 3709582971, 835606218, 2411949883,
    2735205030, 756421180, 2175209704, 1873865952, 2762534237, 4161807854, 3351099340, 181129879,
    3269891896, 776029799, 2218161979, 3001745796, 1866825872, 2133627728, 34862734, 1191934573,
    3102311354, 2916517763, 1012402762, 2184831317, 4257399449, 2899497138, 3818095062, 3030756734,
    1282161629, 420003642, 2326421477, 2741455717, 1278020671, 3744179621, 271777016, 2626330018,
    2560563991, 3055977700, 4233527566, 1228397661, 3595579322, 1077915006, 2395931898, 1851927286,
    3013683506, 1999971931, 3006888962, 1049781534, 1488758959, 3491776230, 104418065, 2448267297,
    3075614115, 3872332600, 891912190, 3936547759, 2269180963, 2633455084, 1047636807, 2604612377,
    2709305729, 1952216715, 207593580, 2849898034, 670771757, 2210471108, 467711165, 263046873,
    3569667915, 1042291111, 3863517079, 1464270005, 2758321352, 3790799816, 2301278724, 3106281430,
    7974801, 2792461636, 555991332, 621766759, 1322453093, 853629228, 686962251, 1455120532,
    957753161, 1802033300, 1021534190, 3486047311, 1902128914, 3701138056, 4176424663, 1795608698,
    560858864, 3737752754, 3141170998, 1553553385, 3367807274, 711546358, 2475125503, 262969859,
    251416325, 2980076994, 1806565895, 969527843, 3529327173, 2736343040, 2987196734, 1649016367,
    2206175811, 3048174801, 3662503553, 3138851612, 2660143804, 1663017612, 1816683231, 411916003,
    3887461314, 2347044079, 1015311755, 1203592432, 2170947766, 2569420716, 813872093, 1105387678,
    1431142475, 220570551, 4243632715, 4179591855, 2607469131, 3090613241, 282341803, 1734241730,
    1391822177, 1001254810, 827927915, 1886687171, 3935097347, 2631788714, 3905163266, 110554195,
    2447955646, 3717202975, 3304793075, 3739614479, 3059127468, 953919171, 2590123714, 1132511021,
    3795593679, 2788030429, 982155079, 3472349556, 859942552, 2681007391, 2299624053, 647443547,
    233600422, 608168955, 3689327453, 1849778220, 1608438222, 3968158357, 2692977776, 2851872572,
    246750393, 3582818628, 3329652309, 4036366910, 1012970930, 950780808, 3959768744, 2538550045,
    191422718, 2658142375, 3276369011, 2927737484, 1234200027, 1920815603, 3536074689, 1535612501,
    2184142071, 3276955054, 428488088, 2378411984, 4059769550, 3913744741, 2732139246, 64369859,
    3755670074, 842839565, 2819894466, 2414718973, 1010060670, 1839715346, 2410311136, 152774329,
    3485009480, 4102101512, 2852724304, 879944024, 1785007662, 2748284463, 1354768064, 3267784736,
    2269127717, 3001240761, 3179796763, 895723219, 865924942, 4291570937, 89355264, 1471026971,
    4114180745, 3201939751, 2867476999, 2460866060, 3603874571, 2238880432, 3308416168, 2072246611,
    2755653839, 3773737248, 1709066580, 4282731467, 2746170170, 2832568330, 433439009, 3175778732,
    26248366, 2551382801, 183214346, 3893339516, 1928168445, 1337157619, 3429096554, 3275170900,
    1782047316, 4264403756, 1876594403, 4289659572, 3223834894, 1728705513, 4068244734, 2867840287,
    1147798696, 302879820, 1730407747, 1923824407, 1180597908, 1569786639, 198796327, 560793173,
    2107345620, 2705990316, 3448772106, 3678374155, 758635715, 884524671, 486356516, 1774865603,
    3881226226, 2635213607, 1181121587, 1508809820, 3178988241, 1594193633, 1235154121, 326117244,
    2304031425, 937054774, 2687415945, 3192389340, 2003740439, 1823766188, 2759543402, 10067710,
    1533252662, 4132494984, 82378136, 420615890, 3467563163, 541562091, 3535949864, 2277319197,
    3330822853, 3215654174, 4113831979, 4204996991, 2162248333, 3255093522, 2219088909, 2978279037,
    255818579, 2859348628, 3097280311, 2569721123, 1861951120, 2907080079, 2719467166, 998319094,
    2521935127, 2404125338, 259456032, 2086860995, 1839848496, 1893547357, 2527997525, 1489393124,
    2860855349, 76448234, 2264934035, 744914583, 2586791259, 1385380501, 66529922, 1819103258,
    1899300332, 2098173828, 1793831094, 276463159, 360132945, 4178212058, 595015228, 177071838,
    2800080290, 1573557746, 1548998935, 378454223, 1460534296, 1116274283, 3112385063, 3709761796,
    827999348, 3580042847, 1913901014, 614021289, 4278528023, 1905177404, 45407939, 3298183234,
    1184848810, 3644926330, 3923635459, 1627046213, 3677876759, 969772772, 1160524753, 1522441192,
    452369933, 1527502551, 832490847, 1003299676, 1071381111, 2891255476, 973747308, 4086897108,
    1847554542, 3895651598, 2227820339, 1621250941, 2881344691, 3583565821, 3510404498, 849362119,
    862871471, 797858058, 2867774932, 2821282612, 3272403146, 3997979905, 209178708, 1805135652,
    6783381, 2823361423, 792580494, 4263749770, 776439581, 3798193823, 2853444094, 2729507474,
    1071873341, 1329010206, 1289336450, 3327680758, 2011491779, 80157208, 922428856, 1158943220,
    1667230961, 2461022820, 2608845159, 387516115, 3345351910, 1495629111, 4098154157, 3156649613,
    3525698599, 4134908037, 446713264, 2137537399, 3617403512, 813966752, 1157943946, 3734692965,
    1680301658, 3180398473, 3509854711, 2228114612, 1008102291, 486805123, 863791847, 3189125290,
    1050308116, 3777341526, 4291726501, 844061465, 1347461791, 2826481581, 745465012, 2055805750,
    4260209475, 2386693097, 2980646741, 447229436, 2077782664, 1232942813, 4023002732, 1399011509,
    3140569849, 2579909222, 3794857471, 900758066, 2887199683, 1720257997, 3367494931, 2668921229,
    955539029, 3818726432, 1105704962, 3889207255, 2277369307, 2746484505, 1761846513, 2413916784,
    2685127085, 4240257943, 1166726899, 4215215715, 3082092067, 3960461946, 1663304043, 2087473241,
    4162589986, 2507310778, 1579665506, 767234210, 970676017, 492207530, 1441679602, 1314785090,
    3262202570, 3417091742, 1561989210, 3011406780, 1146609202, 3262321040, 1374872171, 1634688712,
    1280458888, 2230023982, 419323804, 3262899800, 39783310, 1641619040, 1700368658, 2207946628,
    2571300939, 2424079766, 780290914, 2715195096, 3390957695, 163151474, 2309534542, 1860018424,
    555755123, 280320104, 1604831083, 2713022383, 1728987441, 3639955502, 623065489, 3828630947,
    4275479050, 3516347383, 2343951195, 2430677756, 635534992, 3868699749, 808442435, 3070644069,
    4282166003, 2093181383, 2023555632, 1568662086, 3422372620, 4134522350, 3016979543, 3259320234,
    2888030729, 3185253876, 4258779643, 1267304371, 1022517473, 815943045, 929020012, 2995251018,
    3371283296, 3608029049, 2018485115, 122123397, 2810669150, 1411365618, 1238391329, 1186786476,
    3155969091, 2242941310, 1765554882, 279121160, 4279838515, 1641578514, 3796324015, 13351065,
    103516986, 1609694427, 551411743, 2493771609, 1316337047, 3932650856, 4189700203, 463397996,
    2937735066, 1855616529, 2626847990, 55091862, 3823351211, 753448970, 4045045500, 1274127772,
    1124182256, 92039808, 2126345552, 425973257, 386287896, 2589870191, 1987762798, 4084826973,
    2172456685, 3366583455, 3602966653, 2378803535, 2901764433, 3716929006, 3710159000, 2653449155,
    3469742630, 3096444476, 3932564653, 2595257433, 318974657, 3146202484, 853571438, 144400272,
    3768408841, 782634401, 2161109003, 570039522, 1886241521, 14249488, 2230804228, 1604941699,
    3928713335, 3921942509, 2155806892, 134366254, 430507376, 1924011722, 276713377, 196481886,
    3614810992, 1610021185, 1785757066, 851346168, 3761148643, 2918835642, 3364422385, 3012284466,
    3735958851, 2643153892, 3778608231, 1164289832, 205853021, 2876112231, 3503398282, 3078397001,
    3472037921, 1748894853, 2740861475, 316056182, 1660426908, 168885906, 956005527, 3984354789,
    566521563, 1001109523, 1216710575, 2952284757, 3834433081, 3842608301, 2467352408, 3974441264,
    3256601745, 1409353924, 1329904859, 2307560293, 3125217879, 3622920184, 3832785684, 3882365951,
    2308537115, 2659155028, 1450441945, 3532257603, 3186324194, 1225603425, 1124246549, 175808705,
    3009142319, 2796710159, 3651990107, 160762750, 1902254979, 1698648476, 1134980669, 497144426,
    3302689335, 4057485630, 3603530763, 4087252587, 427812652, 286876201, 823134128, 1627554964,
    3745564327, 2589226092, 4202024494, 62878473, 3275585894, 3987124064, 2791777159, 1916869511,
    2585861905, 1375038919, 1403421920, 60249114, 3811870450, 3021498009, 2612993202, 528933105,
    2757361321, 3341402964, 2621861700, 273128190, 4015252178, 3094781002, 1621621288, 2337611177,
    1796718448, 1258965619, 4241913140, 2138560392, 3022190223, 4174180924, 450094611, 3274724580,
    617150026, 2704660665, 1469700689, 1341616587, 356715071, 1188789960, 2278869135, 1766569160,
    2795896635, 57824704, 2893496380, 1235723989, 1630694347, 3927960522, 428891364, 1814070806,
    2287999787, 4125941184, 3968103889, 3548724050, 1025597707, 1404281500, 2002212197, 92429143,
    2313943944, 2403086080, 3006180634, 3561981764, 1671860914, 1768520622, 1803542985, 844848113,
    3006139921, 1410888995, 1157749833, 2125704913, 1789979528, 1799263423, 741157179, 2405862309,
    767040434, 2655241390, 3663420179, 2172009096, 2511931187, 1680542666, 231857466, 1154981000,
    157168255, 1454112128, 3505872099, 1929775046, 2309422350, 2143329496, 2960716902, 407610648,
    2938108129, 2581749599, 538837155, 2342628867, 430543915, 740188568, 1937713272, 3315215132,
    2085587024, 4030765687, 766054429, 3517641839, 689721775, 1294158986, 1753287754, 4202601348,
    1974852792, 33459103, 3568087535, 3144677435, 1686130825, 4134943013, 3005738435, 3599293386,
    426570142, 754104406, 3660892564, 1964545167, 829466833, 821587464, 1746693036, 1006492428,
    1595312919, 1256599985, 1024482560, 1897312280, 2902903201, 691790057, 1037515867, 3176831208,
    1968401055, 2173506824, 1089055278, 1748401123, 2941380082, 968412354, 1818753861, 2973200866,
    3875951774, 1119354008, 3988604139, 1647155589, 2232450826, 3486058011, 3655784043, 3759258462,
    847163678, 1082052057, 989516446, 2871541755, 3196311070, 3929963078, 658187585, 3664944641,
    2175149170, 2203709147, 2756014689, 2456473919, 3890267390, 1293787864, 2830347984, 3059280931,
    4158802520, 1561677400, 2586570938, 783570352, 1355506163, 31495586, 3789437343, 3340549429,
    2092501630, 896419368, 671715824, 3530450081, 3603554138, 1055991716, 3442308219, 1499434728,
    3130288473, 3639507000, 17769680, 2259741420, 487032199, 4227143402, 3693771256, 1880482820,
    3924810796, 381462353, 4017855991, 2452034943, 2736680833, 2209866385, 2128986379, 437874044,
    595759426, 641721026, 1636065708, 3899136933, 629879088, 3591174506, 351984326, 2638783544,
    2348444281, 2341604660, 2123933692, 143443325, 1525942256, 364660499, 599149312, 939093251,
    1523003209, 106601097, 376589484, 1346282236, 1297387043, 764598052, 3741218111, 933457002,
    1886424424, 3219631016, 525405256, 3014235619, 323149677, 2038881721, 4100129043, 2851715101,
    2984028078, 1888574695, 2014194741, 3515193880, 4180573530, 3461824363, 2641995497, 3179230245,
    2902294983, 2217320456, 4040852155, 1784656905, 3311906931, 87498458, 2752971818, 2635474297,
    2831215366, 3682231106, 2920043893, 3772929704, 2816374944, 309949752, 2383758854, 154870719,
    385111597, 1191604312, 1840700563, 872191186, 2925548701, 1310412747, 2102066999, 1504727249,
    3574298750, 1191230036, 3330575266, 3180292097, 3539347721, 681369118, 3305125752, 3648233597,
    950049240, 4173257693, 1760124957, 512151405, 681175196, 580563018, 1169662867, 4015033554,
    2687781101, 699691603, 2673494188, 1137221356, 123599888, 472658308, 1053598179, 1012713758,
    3481064843, 3759461013, 3981457956, 3830587662, 1877191791, 3650996736, 988064871, 3515461600,
    4089077232, 2225147448, 1249609188, 2643151863, 3896204135, 2416995901, 1397735321, 3460025646,
];

#[test]
fn test_untemper() {
    let x = ::rand::thread_rng().gen::<u32>();
    assert_eq!(x, untemper(temper(x)));
}

#[test]
fn test_recovery() {
    let seed = ::rand::thread_rng().gen::<u32>();
    let mut orig_mt: MT19937 = SeedableRng::from_seed(seed);
    // skip some samples so the RNG is in an intermediate state
    let to_skip = ::rand::thread_rng().gen_range(1, N);
    for _ in 0..to_skip {
        orig_mt.next_u32();
    }
    let samples = orig_mt.gen_iter::<u32>().take(N).collect::<Vec<_>>();
    let mut recovered_mt = MT19937::recover(&samples[..]);
    for _ in 0..N * 2 {
        assert!(orig_mt.next_u32() == recovered_mt.next_u32());
    }
}

// Note: At the time I'm writing this, the `derive` attribute does not
// work for large-ish arrays, so these traits below that are usually
// derived must be manually implemented.

impl Clone for MT19937 {
    #[inline(always)]
    fn clone(&self) -> MT19937 {
        *self
    }
}

impl Debug for MT19937 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("MT19937")
            .field("idx", &self.idx)
            .field("state", &&self.state[..])
            .finish()
    }
}

impl Eq for MT19937 {}

impl Hash for MT19937 {
    fn hash<H: Hasher>(&self, hasher_state: &mut H) {
        self.idx.hash(hasher_state);
        for x in self.state.iter() {
            x.0.hash(hasher_state)
        }
    }
}

impl Ord for MT19937 {
    fn cmp(&self, other: &MT19937) -> Ordering {
        match Ord::cmp(&self.idx, &other.idx) {
            Ordering::Equal => Ord::cmp(&self.state[..], &other.state[..]),
            ordering => ordering,
        }
    }
}

impl PartialEq for MT19937 {
    fn eq(&self, other: &MT19937) -> bool {
        self.idx == other.idx
            && Iterator::zip(self.state.iter(), other.state.iter()).all(|(l, r)| l == r)
    }
}

impl PartialOrd for MT19937 {
    fn partial_cmp(&self, other: &MT19937) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}
