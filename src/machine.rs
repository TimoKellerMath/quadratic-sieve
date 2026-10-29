/// The caches of the machine the sieve is tuned for.
///
/// The defaults, [`Caches::TUNED`], describe the machine on which the parameters
/// were measured, an AMD Ryzen 7 PRO 6850U (Zen 3+, 8 cores with 2 hardware threads
/// each): 32 KiB of L1d and 512 KiB of L2 per core, and 16 MiB of L3 shared by all
/// cores. [`Caches::from_env`] reads the sizes of another machine from
/// `SIQS_L1D_KIB`, `SIQS_L2_KIB` and `SIQS_L3_KIB`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Caches {
    /// The size of a core's L1 data cache, in bytes.
    pub l1d: usize,
    /// The size of a core's L2 cache, in bytes.
    pub l2: usize,
    /// The size of the L3 cache shared by all cores, in bytes.
    pub l3: usize,
}

impl Caches {
    /// The machine the parameters were measured on.
    pub const TUNED: Caches = Caches {
        l1d: 32 << 10,
        l2: 512 << 10,
        l3: 16 << 20,
    };

    /// [`Caches::TUNED`], with each size replaced by its environment variable, in
    /// KiB, if that is set.
    pub fn from_env() -> Caches {
        let kib = |name: &str, default: usize| {
            std::env::var(name)
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .map_or(default, |kib| kib << 10)
        };
        Caches {
            l1d: kib("SIQS_L1D_KIB", Caches::TUNED.l1d),
            l2: kib("SIQS_L2_KIB", Caches::TUNED.l2),
            l3: kib("SIQS_L3_KIB", Caches::TUNED.l3),
        }
    }

    /// The size of a sieve block, a power of two: the largest one up to a quarter of
    /// the L2, which was the fastest on the tuned machine (128 KiB).
    pub fn sieve_block_size(&self) -> usize {
        let quarter = (self.l2 / 4).max(1);
        1 << quarter.ilog2()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sieve_block_is_a_quarter_of_the_l2() {
        assert_eq!(Caches::TUNED.sieve_block_size(), 128 << 10);
        let with_l2 = |l2| Caches {
            l2,
            ..Caches::TUNED
        };
        assert_eq!(with_l2(1 << 20).sieve_block_size(), 256 << 10);
        // rounded down to a power of two
        assert_eq!(with_l2(1280 << 10).sieve_block_size(), 256 << 10);
        assert_eq!(with_l2(3 << 20).sieve_block_size(), 512 << 10);
        assert_eq!(with_l2(0).sieve_block_size(), 1);
    }
}
