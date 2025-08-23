pub mod omega;
pub mod tutorial;
pub mod quantum;
pub mod grover;
pub mod shor;
pub mod information_flow;
pub mod information_flow_alt;
pub mod lagrangian;
pub mod fundamental_physics;
pub mod physics_imax;
#[cfg(test)]
pub mod stress_tests;
#[cfg(test)]
pub mod debug_overflow;
// #[cfg(test)]
// pub mod real_world_examples;
// #[cfg(test)]
// pub mod simple_examples;
#[cfg(test)]
pub mod minimal_examples;
#[cfg(test)]
pub mod v2_prototype;
#[cfg(test)]
pub mod theory_verification;
pub mod total_lang;

pub use omega::Omega;
pub use omega::ThermoOmega;
pub use omega::ComputationBuilder;
