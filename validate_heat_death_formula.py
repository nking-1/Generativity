import math
c = 2.99792458e8      # speed of light
G = 6.67430e-11       # gravitational constant
h_bar = 1.054571817e-34  # reduced Planck
k_B = 1.380649e-23    # Boltzmann
Lambda = 1.089e-52    # cosmological

sin_pi_3 = math.sin(math.pi / 3)
kappa = 8 * math.pi * G / (c**4)
t_planck = math.sqrt((h_bar * G) / (c**5))

f1 = sin_pi_3 * (c**4 / (G * h_bar * math.sqrt(Lambda))) * k_B**2
f2 = sin_pi_3 * (8 * math.pi / (kappa * h_bar * math.sqrt(Lambda))) * k_B**2
f3 = sin_pi_3 / (t_planck**2 * c * math.sqrt(Lambda)) * k_B**2

print(f"Form 1: {f1:.2e}")
print(f"Form 2: {f2:.2e}")
print(f"Form 3: {f3:.2e}")
