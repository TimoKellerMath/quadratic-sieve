pub const PREC: u32 = 32;
pub const SCALE_LOGS: u32 = 1024; // compute log_2(p) * SCALE_LOGS insteaf of log_2(p), so we can work with rounded logs, i.e., u32's