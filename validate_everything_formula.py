import math

# Fundamental Constants
c = 2.99792458e8          # speed of light (m/s)
G = 6.67430e-11           # gravitational constant (m^3/kg/s^2)
h_bar = 1.054571817e-34   # reduced Planck's constant (J·s)
k_B = 1.380649e-23        # Boltzmann's constant (J/K)
Lambda = 1.089e-52        # Cosmological constant (1/m^2)
alpha = 1/137             # Fine-structure constant (electromagnetic interaction)
alpha_s = 0.118           # Strong interaction coupling constant
G_F = 1.1663787e-5        # Fermi constant (GeV^-2)

# Energy Scales
m_e = 9.10938356e-31      # Electron mass (kg)
E_em = m_e * c**2         # Electron rest energy (J)
Lambda_QCD = 0.2e9 * 1.60218e-19  # QCD scale in J (0.2 GeV)
E_weak = 100e9 * 1.60218e-19  # Electroweak scale (100 GeV in J)

# Derived Constants
sin_pi_3 = math.sin(math.pi / 3)  # Sin(pi/3) factor
kappa = 8 * math.pi * G / c**4    # Einstein's gravitational constant
t_planck = math.sqrt(h_bar * G / c**5)  # Planck time (s)

# Gravity & Cosmology Information Flow (Three Forms)
I_max_gravity_1 = sin_pi_3 * (c**4 / (G * h_bar * math.sqrt(Lambda))) * k_B**2
I_max_gravity_2 = sin_pi_3 * (8 * math.pi / (kappa * h_bar * math.sqrt(Lambda))) * k_B**2
I_max_gravity_3 = sin_pi_3 / (t_planck**2 * c * math.sqrt(Lambda)) * k_B**2

# Electromagnetic Information Flow
I_max_em = alpha * (k_B * E_em / h_bar)

# Strong Interaction Information Flow
I_max_strong = alpha_s * (k_B * Lambda_QCD / h_bar)

# Weak Interaction Information Flow
I_max_weak = G_F * (k_B * E_weak**3 / h_bar)

# Print results
print("Maximum Information Flow (J^2 / K^2 / s):")
print(f"Gravity Form 1: {I_max_gravity_1:.2e}")
print(f"Gravity Form 2: {I_max_gravity_2:.2e}")
print(f"Gravity Form 3: {I_max_gravity_3:.2e}")

print("Maximum Information Flow (J / K / s):")
print(f"Electromagnetic: {I_max_em:.2e}")
print(f"Strong Interaction: {I_max_strong:.2e}")
print(f"Weak Interaction: {I_max_weak:.2e}")

