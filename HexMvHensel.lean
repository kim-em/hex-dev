/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexMvHensel.Shift
public import HexMvHensel.Modulus
public import HexMvHensel.Uni
public import HexMvHensel.Diophantine
public import HexMvHensel.Seed
public import HexMvHensel.Cert
public import HexMvHensel.Lift
public import HexMvHensel.Complete
public import HexMvHensel.KernelTests
public import HexMvHensel.ShiftTests
public import HexMvHensel.UniTests
public import HexMvHensel.DiophantineTests
public import HexMvHensel.SeedTests
public import HexMvHensel.CertTests
public import HexMvHensel.LiftTests
public import HexMvHensel.CompleteTests

public section

/-!
Multivariate Hensel lifting infrastructure.

The current module exposes the complete checked multivariate Hensel lift:
coordinates and modulus arithmetic, univariate and multivariate correction
solvers, seeding and validation, stagewise lifting, reconstruction, and the
independent certificate checker, and conditional completeness and uniqueness
contracts with an executable shifted-factor coefficient bound.
-/
