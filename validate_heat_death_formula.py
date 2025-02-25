import math
import numpy as np

# Fundamental constants in SI units
c = 2.99792458e8      # speed of light (m/s)
G = 6.67430e-11       # gravitational constant (m³/kg/s²)
h_bar = 1.054571817e-34  # reduced Planck constant (J·s)
k_B = 1.380649e-23    # Boltzmann constant (J/K)
Lambda = 1.089e-52    # cosmological constant (m⁻²)
kappa = 8 * math.pi * G / (c**4)  # Einstein's constant

# Common factor
sin_pi_3 = math.sin(math.pi / 3)

# First form: sin(π/3)·(c⁴/Gℏ√Λ)·kB²
form1 = sin_pi_3 * (c**4 / (G * h_bar * math.sqrt(Lambda))) * k_B**2

# Second form: sin(π/3)·8π/κℏ√Λ·kB²
form2 = sin_pi_3 * (8 * math.pi / (kappa * h_bar * math.sqrt(Lambda))) * k_B**2

# Third form: sin(π/3)/tPlanck²c√Λ·kB²
t_planck = math.sqrt((h_bar * G) / (c**5))
form3 = sin_pi_3 / (t_planck**2 * c * math.sqrt(Lambda)) * k_B**2

print(f"Form 1: {form1:.2e} J²/(K²·s)")
print(f"Form 2: {form2:.2e} J²/(K²·s)")
print(f"Form 3: {form3:.2e} J²/(K²·s)")

# Check relative differences
rel_diff_12 = abs(form1 - form2) / form1
rel_diff_13 = abs(form1 - form3) / form1
rel_diff_23 = abs(form2 - form3) / form2

print(f"\nRelative differences:")
print(f"Between forms 1 and 2: {rel_diff_12:.2e}")
print(f"Between forms 1 and 3: {rel_diff_13:.2e}")
print(f"Between forms 2 and 3: {rel_diff_23:.2e}")
