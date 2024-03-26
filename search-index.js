var searchIndex = new Map(JSON.parse('[\
["rand_core",{"doc":"Random number generation traits","t":"TKKFTKRKMCNNNMNNNNNMCNCMMNNMNNNFFKRRNNNNNNNOONNNNNNNNNNMNNNNNNNNNNNNNNNNNNNNNNNNHHHHHHHH","n":["CUSTOM_START","CryptoRng","CryptoRngCore","Error","INTERNAL_START","RngCore","Seed","SeedableRng","as_rngcore","block","borrow","borrow_mut","code","fill_bytes","fmt","fmt","from","from","from_rng","from_seed","impls","into","le","next_u32","next_u64","raw_os_error","seed_from_u64","try_fill_bytes","try_from","try_into","type_id","BlockRng","BlockRng64","BlockRngCore","Item","Results","as_rngcore","borrow","borrow","borrow_mut","borrow_mut","clone","clone","core","core","fill_bytes","fill_bytes","fmt","fmt","from","from","from_rng","from_rng","from_seed","from_seed","generate","generate_and_set","generate_and_set","index","index","into","into","new","new","next_u32","next_u32","next_u64","next_u64","reset","reset","seed_from_u64","seed_from_u64","try_fill_bytes","try_fill_bytes","try_from","try_from","try_into","try_into","type_id","type_id","fill_bytes_via_next","fill_via_u32_chunks","fill_via_u64_chunks","next_u32_via_fill","next_u64_via_fill","next_u64_via_u32","read_u32_into","read_u64_into"],"q":[[0,"rand_core"],[31,"rand_core::block"],[80,"rand_core::impls"],[86,"rand_core::le"],[88,"core::num::nonzero"],[89,"core::option"],[90,"core::fmt"],[91,"core::fmt"],[92,"core::marker"],[93,"core::default"],[94,"core::convert"],[95,"core::any"],[96,"core::clone"],[97,"core::fmt"]],"d":["Codes at or above this point can be used by users to …","A marker trait used to indicate that an <code>RngCore</code> or …","An extension trait that is automatically implemented for …","Error type of random number generators","Codes below this point represent OS Errors (i.e. positive …","The core of a random number generator.","Seed type, which is restricted to types …","A random number generator that can be explicitly seeded.","Upcast to an <code>RngCore</code> trait object.","The <code>BlockRngCore</code> trait and implementation helpers","","","Retrieve the error code, if any.","Fill <code>dest</code> with random data.","","","Returns the argument unchanged.","","Create a new PRNG seeded from another <code>Rng</code>.","Create a new PRNG using the given seed.","Helper functions for implementing <code>RngCore</code> functions.","Calls <code>U::from(self)</code>.","Little-Endian utilities","Return the next random <code>u32</code>.","Return the next random <code>u64</code>.","Extract the raw OS error code (if this error came from the …","Create a new PRNG using a <code>u64</code> seed.","Fill <code>dest</code> entirely with random data.","","","","A wrapper type implementing <code>RngCore</code> for some type …","A wrapper type implementing <code>RngCore</code> for some type …","A trait for RNGs which do not generate random numbers …","Results element type, e.g. <code>u32</code>.","Results type. This is the ‘block’ an RNG implementing …","","","","","","","","The <em>core</em> part of the RNG, implementing the <code>generate</code> …","The <em>core</em> part of the RNG, implementing the <code>generate</code> …","","","","","Returns the argument unchanged.","Returns the argument unchanged.","","","","","Generate a new block of results.","Generate a new set of results immediately, setting the …","Generate a new set of results immediately, setting the …","Get the index into the result buffer.","Get the index into the result buffer.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Create a new <code>BlockRng</code> from an existing RNG implementing …","Create a new <code>BlockRng</code> from an existing RNG implementing …","","","","","Reset the number of available results. This will force a …","Reset the number of available results. This will force a …","","","","","","","","","","","Implement <code>fill_bytes</code> via <code>next_u64</code> and <code>next_u32</code>, …","Implement <code>fill_bytes</code> by reading chunks from the output …","Implement <code>fill_bytes</code> by reading chunks from the output …","Implement <code>next_u32</code> via <code>fill_bytes</code>, little-endian order.","Implement <code>next_u64</code> via <code>fill_bytes</code>, little-endian order.","Implement <code>next_u64</code> via <code>next_u32</code>, little-endian order.","Reads unsigned 32 bit integers from <code>src</code> into <code>dst</code>.","Reads unsigned 64 bit integers from <code>src</code> into <code>dst</code>."],"i":[3,0,0,0,3,0,12,0,1,0,3,3,3,2,3,3,3,3,12,12,0,3,0,2,2,3,12,2,3,3,3,0,0,0,23,23,21,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,23,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,21,24,0,0,0,0,0,0,0,0],"f":"````````{bd}`{ce{}{}}0{f{{j{h}}}}{{d{n{l}}}A`}{{fAb}Ad}0{cc{}}{hf}{c{{Aj{{Ah{}{{Af{e}}}}f}}}d{AlAn{B`{{n{l}}}}}}{c{{Ah{}{{Af{c}}}}}{AlAn{B`{{n{l}}}}}}`7`{dBb}{dBd}{f{{j{Bf}}}}{Bd{{Ah{}{{Af{c}}}}}{AlAn{B`{{n{l}}}}}}{{d{n{l}}}{{Aj{A`f}}}}{c{{Aj{e}}}{}{}}0{cBh{}}`````{cd{}}????{{{Bj{c}}}{{Bj{c}}}{BlBnAl}}{{{C`{c}}}{{C`{c}}}{BlBnAl}}``{{{Bj{c}}{n{l}}}A`{{Bn{}{{Cb{Bb}}}}}}{{{C`{c}}{n{l}}}A`{{Bn{}{{Cb{Bd}}}}}}{{{Bj{c}}Ab}Ad{BnCd}}{{{C`{c}}Ab}Ad{BnCd}}{cc{}}0{c{{Aj{{Bj{e}}f}}}d{BnAh}}{c{{Aj{{C`{e}}f}}}d{BnAh}}{c{{Bj{e}}}{}{BnAh}}{c{{C`{e}}}{}{BnAh}}{{{Bn{}{{Cb{c}}{Cf{e}}}}e}A`{}{{Ch{{n{c}}}}{B`{{n{c}}}}An}}{{{Bj{c}}Cj}A`Bn}{{{C`{c}}Cj}A`Bn}{{{Bj{c}}}CjBn}{{{C`{c}}}CjBn}{ce{}{}}0{c{{Bj{c}}}Bn}{c{{C`{c}}}Bn}{{{Bj{c}}}Bb{{Bn{}{{Cb{Bb}}}}}}{{{C`{c}}}Bb{{Bn{}{{Cb{Bd}}}}}}{{{Bj{c}}}Bd{{Bn{}{{Cb{Bb}}}}}}{{{C`{c}}}Bd{{Bn{}{{Cb{Bd}}}}}}{{{Bj{c}}}A`Bn}{{{C`{c}}}A`Bn}{Bd{{Bj{c}}}{BnAh}}{Bd{{C`{c}}}{BnAh}}{{{Bj{c}}{n{l}}}{{Aj{A`f}}}{{Bn{}{{Cb{Bb}}}}}}{{{C`{c}}{n{l}}}{{Aj{A`f}}}{{Bn{}{{Cb{Bd}}}}}}{c{{Aj{e}}}{}{}}000{cBh{}}0{{c{n{l}}}A`{dAl}}{{{n{Bb}}{n{l}}}{{Cl{CjCj}}}}{{{n{Bd}}{n{l}}}{{Cl{CjCj}}}}{cBb{dAl}}{cBd{dAl}}0{{{n{l}}{n{Bb}}}A`}{{{n{l}}{n{Bd}}}A`}","c":[],"p":[[10,"CryptoRngCore",0],[10,"RngCore",0],[5,"Error",0],[8,"NonZeroU32",88],[6,"Option",89],[1,"u8"],[1,"slice"],[1,"unit"],[5,"Formatter",90],[8,"Result",90],[17,"Seed"],[10,"SeedableRng",0],[6,"Result",91],[10,"Sized",92],[10,"Default",93],[10,"AsMut",94],[1,"u32"],[1,"u64"],[1,"i32"],[5,"TypeId",95],[5,"BlockRng",31],[10,"Clone",96],[10,"BlockRngCore",31],[5,"BlockRng64",31],[17,"Item"],[10,"Debug",90],[17,"Results"],[10,"AsRef",94],[1,"usize"],[1,"tuple"]],"b":[[14,"impl-Debug-for-Error"],[15,"impl-Display-for-Error"]]}],\
["rand_mt",{"doc":"Mersenne Twister random number generators.","t":"TTIFFIGPPNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNN","n":["DEFAULT_SEED","DEFAULT_SEED","Mt","Mt19937GenRand32","Mt19937GenRand64","Mt64","RecoverRngError","TooFewSamples","TooManySamples","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","clone","clone","clone","clone_into","clone_into","clone_into","cmp","cmp","default","default","eq","eq","eq","fill_bytes","fill_bytes","fill_bytes","fill_bytes","fmt","fmt","fmt","fmt","from","from","from","from","from","from","from","from","from","from_seed","from_seed","hash","hash","hash","into","into","into","new","new","new_unseeded","new_unseeded","new_with_key","new_with_key","next_u32","next_u32","next_u32","next_u32","next_u64","next_u64","next_u64","next_u64","partial_cmp","partial_cmp","recover","recover","reseed","reseed","reseed_with_key","reseed_with_key","to_owned","to_owned","to_owned","to_string","try_fill_bytes","try_fill_bytes","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","type_id","type_id","type_id"],"q":[[0,"rand_mt"],[92,"core::cmp"],[93,"core::fmt"],[94,"core::fmt"],[95,"core::iter::traits::collect"],[96,"core::option"],[97,"core::result"],[98,"alloc::string"],[99,"rand_core::error"],[100,"core::any"]],"d":["Default seed used by <code>Mt19937GenRand32::new_unseeded</code>.","Default seed used by <code>Mt19937GenRand64::new_unseeded</code>.","A type alias for <code>Mt19937GenRand32</code>, 32-bit Mersenne Twister.","The 32-bit flavor of the Mersenne Twister pseudorandom …","The 64-bit flavor of the Mersenne Twister pseudorandom …","A type alias for <code>Mt19937GenRand64</code>, 64-bit Mersenne Twister.","Error returned from fallible Mersenne Twister recovery …","Attempted to recover an RNG with too many samples.","Attempted to recover an RNG with too few samples.","","","","","","","","","","","","","","","Return a new <code>Mt19937GenRand32</code> with the default seed.","Return a new <code>Mt19937GenRand64</code> with the default seed.","","","","Fill a buffer with bytes generated from the RNG.","Fill a buffer with bytes generated from the RNG.","Fill a buffer with bytes generated from the RNG.","Fill a buffer with bytes generated from the RNG.","","","","","Returns the argument unchanged.","Construct a Mersenne Twister RNG from a <code>u32</code> seed.","Recover the internal state of a Mersenne Twister using the …","Construct a Mersenne Twister RNG from 4 bytes.","Construct a Mersenne Twister RNG from a <code>u64</code> seed.","Returns the argument unchanged.","Recover the internal state of a Mersenne Twister using the …","Construct a Mersenne Twister RNG from 8 bytes.","Returns the argument unchanged.","Reseed from a little endian encoded <code>u32</code>.","Reseed from a little endian encoded <code>u64</code>.","","","","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Create a new Mersenne Twister random number generator …","Create a new Mersenne Twister random number generator …","Create a new Mersenne Twister random number generator …","Create a new Mersenne Twister random number generator …","Create a new Mersenne Twister random number generator …","Create a new Mersenne Twister random number generator …","Generate next <code>u32</code> output.","Generate next <code>u32</code> output.","Generate next <code>u32</code> output.","Generate next <code>u32</code> output.","Generate next <code>u64</code> output.","Generate next <code>u64</code> output.","Generate next <code>u64</code> output.","Generate next <code>u64</code> output.","","","Attempt to recover the internal state of a Mersenne …","Attempt to recover the internal state of a Mersenne …","Reseed a Mersenne Twister from a single <code>u32</code>.","Reseed a Mersenne Twister from a single <code>u64</code>.","Reseed a Mersenne Twister from am iterator of <code>u32</code>s.","Reseed a Mersenne Twister from am iterator of <code>u64</code>s.","","","","","Fill a buffer with bytes generated from the RNG.","Fill a buffer with bytes generated from the RNG.","","Attempt to recover the internal state of a Mersenne …","Attempt to recover the internal state of a Mersenne …","","","","","","","",""],"i":[1,2,0,0,0,0,0,3,3,1,2,3,1,2,3,1,2,3,1,2,3,1,2,1,2,1,2,3,1,1,2,2,1,2,3,3,1,1,1,1,2,2,2,2,3,1,2,1,2,3,1,2,3,1,2,1,2,1,2,1,1,2,2,1,1,2,2,1,2,1,2,1,2,1,2,1,2,3,3,1,2,1,1,2,2,3,1,2,3,1,2,3],"f":"`````````{ce{}{}}00000{bb}{dd}{ff}{{ce}h{}{}}00{{bb}j}{{dd}j}{{}b}{{}d}{{bb}l}{{dd}l}{{ff}l}{{b{A`{n}}}h}0{{d{A`{n}}}h}0{{bAb}Ad}{{dAb}Ad}{{fAb}Ad}0{cc{}}{Afb}{{{Ah{Af}}}b}{{{Ah{n}}}b}{Ajd}4{{{Ah{Aj}}}d}{{{Ah{n}}}d}6{cb{}}{cd{}}{{bc}hAl}{{dc}hAl}{{fc}hAl}{ce{}{}}00;8{{}b}{{}d}{cb{{B`{}{{An{Af}}}}}}{cd{{B`{}{{An{Aj}}}}}}{bAf}0{dAf}0{bAj}0{dAj}0{{bb}{{Bb{j}}}}{{dd}{{Bb{j}}}}{c{{Bd{bf}}}{{B`{}{{An{Af}}}}}}{c{{Bd{df}}}{{B`{}{{An{Aj}}}}}}{{bAf}h}{{dAj}h}{{bc}h{{B`{}{{An{Af}}}}}}{{dc}h{{B`{}{{An{Aj}}}}}}{ce{}{}}00{cBf{}}{{b{A`{n}}}{{Bd{hBh}}}}{{d{A`{n}}}{{Bd{hBh}}}}{c{{Bd{e}}}{}{}}{{{A`{Af}}}{{Bd{bc}}}{}}{{{A`{Aj}}}{{Bd{dc}}}{}}22222{cBj{}}00","c":[],"p":[[5,"Mt19937GenRand32",0],[5,"Mt19937GenRand64",0],[6,"RecoverRngError",0],[1,"unit"],[6,"Ordering",92],[1,"bool"],[1,"u8"],[1,"slice"],[5,"Formatter",93],[8,"Result",93],[1,"u32"],[1,"array"],[1,"u64"],[10,"Hasher",94],[17,"Item"],[10,"IntoIterator",95],[6,"Option",96],[6,"Result",97],[5,"String",98],[5,"Error",99],[5,"TypeId",100]],"b":[[28,"impl-Mt19937GenRand32"],[29,"impl-RngCore-for-Mt19937GenRand32"],[30,"impl-Mt19937GenRand64"],[31,"impl-RngCore-for-Mt19937GenRand64"],[34,"impl-Display-for-RecoverRngError"],[35,"impl-Debug-for-RecoverRngError"],[37,"impl-From%3Cu32%3E-for-Mt19937GenRand32"],[38,"impl-From%3C%5Bu32;+N%5D%3E-for-Mt19937GenRand32"],[39,"impl-From%3C%5Bu8;+4%5D%3E-for-Mt19937GenRand32"],[40,"impl-From%3Cu64%3E-for-Mt19937GenRand64"],[42,"impl-From%3C%5Bu64;+NN%5D%3E-for-Mt19937GenRand64"],[43,"impl-From%3C%5Bu8;+8%5D%3E-for-Mt19937GenRand64"],[59,"impl-RngCore-for-Mt19937GenRand32"],[60,"impl-Mt19937GenRand32"],[61,"impl-Mt19937GenRand64"],[62,"impl-RngCore-for-Mt19937GenRand64"],[63,"impl-RngCore-for-Mt19937GenRand32"],[64,"impl-Mt19937GenRand32"],[65,"impl-Mt19937GenRand64"],[66,"impl-RngCore-for-Mt19937GenRand64"]]}]\
]'));
if (typeof exports !== 'undefined') exports.searchIndex = searchIndex;
else if (window.initSearch) window.initSearch(searchIndex);