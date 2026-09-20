/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.Certificate
public section

syntax "cadVanishingInput" : term
macro_rules
  | `(cadVanishingInput) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], cmp := Hex.RCF.Cmp.eq }).imp
    (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], cmp := Hex.RCF.Cmp.eq })))

syntax "cadVanishingCert" : term
macro_rules
  | `(cadVanishingCert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], repeated := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1],
        derivPart := Hex.DensePoly.ofCoeffs #[0, 4, 0, 8], factorScale := 1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], Hex.DensePoly.ofCoeffs #[0, 1, 0, 2],
                Hex.DensePoly.ofCoeffs #[2, 0, -1], Hex.DensePoly.ofCoeffs #[0, -1], Hex.DensePoly.ofCoeffs #[-1]],
            derivScale := 2,
            steps :=
              #[{ leftScale := 2, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 1 },
                { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, -2], rightScale := 5 },
                { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 2 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-1), upper := Dyadic.ofInt (-1) >>> 1, lt := by decide },
            { lower := Dyadic.ofInt 1 >>> 1, upper := Dyadic.ofInt 1, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[1], atomCoeff := Hex.DensePoly.ofCoeffs #[],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[1], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], Hex.DensePoly.ofCoeffs #[0, 1, 0, 2],
                        Hex.DensePoly.ofCoeffs #[2, 0, -1], Hex.DensePoly.ofCoeffs #[0, -1],
                        Hex.DensePoly.ofCoeffs #[-1]],
                    derivScale := 2,
                    steps :=
                      #[{ leftScale := 2, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 1 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, -2], rightScale := 5 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 2 }] } }] },
    iocCmps := Option.none })

syntax "cadNlsatInput" : term
macro_rules
  | `(cadNlsatInput) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[16, 1, -8, 16], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[0, 1], cmp := Hex.RCF.Cmp.lt }).imp
      (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-2, 0, -1, 1], cmp := Hex.RCF.Cmp.lt }))))

syntax "cadNlsatCert" : term
macro_rules
  | `(cadNlsatCert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[0, -32, -2, 0, -17, 9, -24, 16], repeated := Hex.DensePoly.ofCoeffs #[1],
        derivPart := Hex.DensePoly.ofCoeffs #[-32, -4, 0, -68, 45, -144, 112], factorScale := 1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[0, -32, -2, 0, -17, 9, -24, 16],
                Hex.DensePoly.ofCoeffs #[-32, -4, 0, -68, 45, -144, 112],
                Hex.DensePoly.ofCoeffs #[96, 2700, 140, 204, 579, 180],
                Hex.DensePoly.ofCoeffs #[-816, -25830, 4435, -1434, -5304],
                Hex.DensePoly.ofCoeffs #[-18768, -116730, 381791, -274977],
                Hex.DensePoly.ofCoeffs #[111201456, 11215202742, 2853422209],
                Hex.DensePoly.ofCoeffs #[339941260456, 26267727086813], Hex.DensePoly.ofCoeffs #[1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 12544, quotient := Hex.DensePoly.ofCoeffs #[-384, 1792], rightScale := 128 },
                { leftScale := 32400, quotient := Hex.DensePoly.ofCoeffs #[-90768, 20160], rightScale := 9408 },
                { leftScale := 28132416, quotient := Hex.DensePoly.ofCoeffs #[-2812896, -954720], rightScale := 21600 },
                { leftScale := 75612350529, quotient := Hex.DensePoly.ofCoeffs #[2419336482, 1458478008],
                  rightScale := 146523 },
                { leftScale := 8142018302814439681,
                  quotient := Hex.DensePoly.ofCoeffs #[4173333722983253, -784625478764193],
                  rightScale := 1814696412696 },
                { leftScale := 689993486307289375638496969,
                  quotient := Hex.DensePoly.ofCoeffs #[293627888907792225773942, 74952915849463085229917],
                  rightScale := 23087954352462588405419780995450688 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-1), upper := Dyadic.ofInt (-3) >>> 2, lt := by decide },
            { lower := Dyadic.ofInt (-1) >>> 4, upper := Dyadic.ofInt 0, lt := by decide },
            { lower := Dyadic.ofInt 1, upper := Dyadic.ofInt 2, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[16, 1, -8, 16], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -2, 0, -1, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[16, 1, -8, 16], Hex.DensePoly.ofCoeffs #[1, -16, 48],
                        Hex.DensePoly.ofCoeffs #[-289, 4], Hex.DensePoly.ofCoeffs #[-1]],
                    derivScale := 1,
                    steps :=
                      #[{ leftScale := 2304, quotient := Hex.DensePoly.ofCoeffs #[-128, 768], rightScale := 128 },
                        { leftScale := 16, quotient := Hex.DensePoly.ofCoeffs #[13808, 192],
                          rightScale := 3990528 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-32, -2, 0, -17, 9, -24, 16],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[0, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-2, 0, -1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, 16, 1, -8, 16], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-2, 0, -1, 1], Hex.DensePoly.ofCoeffs #[0, -2, 3],
                        Hex.DensePoly.ofCoeffs #[9, 1], Hex.DensePoly.ofCoeffs #[-1]],
                    derivScale := 1,
                    steps :=
                      #[{ leftScale := 9, quotient := Hex.DensePoly.ofCoeffs #[-1, 3], rightScale := 2 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[-29, 3], rightScale := 261 }] } }] },
    iocCmps := Option.none })

syntax "cadCircleParabolaInput" : term
macro_rules
  | `(cadCircleParabolaInput) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[0, 1], cmp := Hex.RCF.Cmp.gt }).imp
      (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[0, -1, 1], cmp := Hex.RCF.Cmp.lt }))))

syntax "cadCircleParabolaCert" : term
macro_rules
  | `(cadCircleParabolaCert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[0, 1, -1, -1, 1, -1, 1], repeated := Hex.DensePoly.ofCoeffs #[0, 1],
        derivPart := Hex.DensePoly.ofCoeffs #[2, -3, -4, 5, -6, 7], factorScale := 1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[0, 1, -1, -1, 1, -1, 1], Hex.DensePoly.ofCoeffs #[1, -2, -3, 4, -5, 6],
                Hex.DensePoly.ofCoeffs #[-1, -28, 27, 14, -7], Hex.DensePoly.ofCoeffs #[0, 3, 0, -4],
                Hex.DensePoly.ofCoeffs #[4, 70, -87], Hex.DensePoly.ofCoeffs #[32, -49], Hex.DensePoly.ofCoeffs #[-1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 36, quotient := Hex.DensePoly.ofCoeffs #[-1, 6], rightScale := 1 },
                { leftScale := 49, quotient := Hex.DensePoly.ofCoeffs #[-49, -42], rightScale := 504 },
                { leftScale := 16, quotient := Hex.DensePoly.ofCoeffs #[-56, 28], rightScale := 4 },
                { leftScale := 7569, quotient := Hex.DensePoly.ofCoeffs #[280, 348], rightScale := 35 },
                { leftScale := 2401, quotient := Hex.DensePoly.ofCoeffs #[-646, 4263], rightScale := 30276 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-1), upper := Dyadic.ofInt (-3) >>> 2, lt := by decide },
            { lower := Dyadic.ofInt (-1) >>> 2, upper := Dyadic.ofInt 0, lt := by decide },
            { lower := Dyadic.ofInt 3 >>> 2, upper := Dyadic.ofInt 13 >>> 4, lt := by decide },
            { lower := Dyadic.ofInt 15 >>> 4, upper := Dyadic.ofInt 1, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -1, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], Hex.DensePoly.ofCoeffs #[0, 1, 0, 2],
                        Hex.DensePoly.ofCoeffs #[2, 0, -1], Hex.DensePoly.ofCoeffs #[0, -1],
                        Hex.DensePoly.ofCoeffs #[-1]],
                    derivScale := 2,
                    steps :=
                      #[{ leftScale := 2, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 1 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, -2], rightScale := 5 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 2 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[1, -1, -1, 1, -1, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[0, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[0, -1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-1, 0, 1, 0, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[0, -1, 1], Hex.DensePoly.ofCoeffs #[-1, 2],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 1,
                    steps := #[{ leftScale := 4, quotient := Hex.DensePoly.ofCoeffs #[-1, 2], rightScale := 1 }] } }] },
    iocCmps := Option.none })

syntax "cadCirclesInput" : term
macro_rules
  | `(cadCirclesInput) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-3, 0, 4], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[0, 1], cmp := Hex.RCF.Cmp.gt }).imp
      (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-1, 2], cmp := Hex.RCF.Cmp.gt }))))

syntax "cadCirclesCert" : term
macro_rules
  | `(cadCirclesCert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[0, 3, -6, -4, 8], repeated := Hex.DensePoly.ofCoeffs #[1],
        derivPart := Hex.DensePoly.ofCoeffs #[3, -12, -12, 32], factorScale := 1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[0, 3, -6, -4, 8], Hex.DensePoly.ofCoeffs #[3, -12, -12, 32],
                Hex.DensePoly.ofCoeffs #[-1, -20, 36], Hex.DensePoly.ofCoeffs #[-2, 5], Hex.DensePoly.ofCoeffs #[1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 1024, quotient := Hex.DensePoly.ofCoeffs #[-32, 256], rightScale := 96 },
                { leftScale := 1296, quotient := Hex.DensePoly.ofCoeffs #[208, 1152], rightScale := 2048 },
                { leftScale := 25, quotient := Hex.DensePoly.ofCoeffs #[-28, 180], rightScale := 81 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-1), upper := Dyadic.ofInt (-3) >>> 2, lt := by decide },
            { lower := Dyadic.ofInt (-1) >>> 3, upper := Dyadic.ofInt 0, lt := by decide },
            { lower := Dyadic.ofInt 3 >>> 3, upper := Dyadic.ofInt 1 >>> 1, lt := by decide },
            { lower := Dyadic.ofInt 3 >>> 2, upper := Dyadic.ofInt 1, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[-3, 0, 4], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -1, 2], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-3, 0, 4], Hex.DensePoly.ofCoeffs #[0, 1],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 8,
                    steps := #[{ leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 4], rightScale := 3 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[3, -6, -4, 8], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[0, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-1, 2], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -3, 0, 4], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-1, 2], Hex.DensePoly.ofCoeffs #[1]], derivScale := 2,
                    steps := #[] } }] },
    iocCmps := Option.none })

syntax "cadKahanInput" : term
macro_rules
  | `(cadKahanInput) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-2, 0, 1], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[1, -1], cmp := Hex.RCF.Cmp.lt }).imp
      ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-2, 1], cmp := Hex.RCF.Cmp.lt }).imp
        (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-60, 8, 5], cmp := Hex.RCF.Cmp.lt })))))

syntax "cadKahanCert" : term
macro_rules
  | `(cadKahanCert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[240, -392, 28, 210, -84, -7, 5], repeated := Hex.DensePoly.ofCoeffs #[1],
        derivPart := Hex.DensePoly.ofCoeffs #[392, -56, -630, 336, 35, -30], factorScale := -1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[240, -392, 28, 210, -84, -7, 5],
                Hex.DensePoly.ofCoeffs #[-392, 56, 630, -336, -35, 30],
                Hex.DensePoly.ofCoeffs #[-40456, 58408, -7770, -16548, 5285],
                Hex.DensePoly.ofCoeffs #[-327696, 2026508, -2134160, 595007],
                Hex.DensePoly.ofCoeffs #[247988228, -336633172, 108578631],
                Hex.DensePoly.ofCoeffs #[-67986921664, 46865069165], Hex.DensePoly.ofCoeffs #[1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 900, quotient := Hex.DensePoly.ofCoeffs #[-35, 150], rightScale := 5 },
                { leftScale := 27931225, quotient := Hex.DensePoly.ofCoeffs #[311465, 158550], rightScale := 5040 },
                { leftScale := 354033330049, quotient := Hex.DensePoly.ofCoeffs #[1432859764, 3144611995],
                  rightScale := 55862450 },
                { leftScale := 11789319109834161, quotient := Hex.DensePoly.ofCoeffs #[-31425077362756, 64605045495417],
                  rightScale := 57801360008 },
                { leftScale := 2196334707840233797225,
                  quotient := Hex.DensePoly.ofCoeffs #[-8394410008831979396, 5088545051656013115],
                  rightScale := 26044943393760044854374967644 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-6), upper := Dyadic.ofInt (-4), lt := by decide },
            { lower := Dyadic.ofInt (-2), upper := Dyadic.ofInt (-1), lt := by decide },
            { lower := Dyadic.ofInt 3 >>> 2, upper := Dyadic.ofInt 1, lt := by decide },
            { lower := Dyadic.ofInt 11 >>> 3, upper := Dyadic.ofInt 3 >>> 1, lt := by decide },
            { lower := Dyadic.ofInt 31 >>> 4, upper := Dyadic.ofInt 2, lt := by decide },
            { lower := Dyadic.ofInt 5 >>> 1, upper := Dyadic.ofInt 3, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[-2, 0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-120, 196, -74, -7, 5],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-2, 0, 1], Hex.DensePoly.ofCoeffs #[0, 1],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 2,
                    steps := #[{ leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 2 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[-1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-240, 152, 124, -86, -2, 5],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := -1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-1, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-2, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-120, 136, 54, -78, 3, 5],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-2, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-60, 8, 5], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-4, 6, 0, -3, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-60, 8, 5], Hex.DensePoly.ofCoeffs #[4, 5],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 2,
                    steps :=
                      #[{ leftScale := 25, quotient := Hex.DensePoly.ofCoeffs #[20, 25], rightScale := 1580 }] } }] },
    iocCmps := Option.none })

syntax "cadSphereInput" : term
macro_rules
  | `(cadSphereInput) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[3, -1], cmp := Hex.RCF.Cmp.lt }).imp
      ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-4, 1], cmp := Hex.RCF.Cmp.lt }).imp
        (Hex.RCF.Formula.atom
          { p := Hex.DensePoly.ofCoeffs #[144, 0, -1213, 0, 250, 0, -13], cmp := Hex.RCF.Cmp.gt })))))

syntax "cadSphereCert" : term
macro_rules
  | `(cadSphereCert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[576, -144, -10612, 2653, 50096, -12524, -14904, 3726, 1520, -380, -52, 13],
        repeated := Hex.DensePoly.ofCoeffs #[-3, 1],
        derivPart :=
          Hex.DensePoly.ofCoeffs #[-336, -21240, 11491, 200677, -79221, -90783, 30597, 12423, -3839, -533, 156],
        factorScale := 1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[576, -144, -10612, 2653, 50096, -12524, -14904, 3726, 1520, -380, -52, 13],
                Hex.DensePoly.ofCoeffs #[-144, -21224, 7959, 200384, -62620, -89424, 26082, 12160, -3420, -520, 143],
                Hex.DensePoly.ofCoeffs #[-8640, 12592, 127344, -129375, -450864, 148035, 89424, -26573, -4560, 1305],
                Hex.DensePoly.ofCoeffs
                  #[261360, 18842264, -8033985, -173037816, 52042437, 35387016, -10558827, -1827112, 543447],
                Hex.DensePoly.ofCoeffs
                  #[41735899080, -87523418684, -387982385928, 804784382730, 91810620648, -167269989615, -5348092968,
                    8767558441],
                Hex.DensePoly.ofCoeffs
                  #[-42691285082928, -7664436085792, 397900913640081, 67700819597152, -103073401228779, -6723577410112,
                    6380336763522],
                Hex.DensePoly.ofCoeffs
                  #[-1055600329819152, 376698259291592, 9658804606527336, -3375583521717179, -960093350632728,
                    335361651122075],
                Hex.DensePoly.ofCoeffs
                  #[6770458392317244304, 581825206326164416, -62063347887890140147, -127846214138912192,
                    6182777946357283531],
                Hex.DensePoly.ofCoeffs
                  #[29597146553273307154, -247811764359161605271, -148306490025177628034, 72223740632431780063],
                Hex.DensePoly.ofCoeffs #[-55267777164877549801, -1404516720736604067840, 513127285435332689057],
                Hex.DensePoly.ofCoeffs #[-102102028800584, 306649110857049], Hex.DensePoly.ofCoeffs #[1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 20449, quotient := Hex.DensePoly.ofCoeffs #[-676, 1859], rightScale := 1352 },
                { leftScale := 1703025, quotient := Hex.DensePoly.ofCoeffs #[-26520, 186615], rightScale := 1815 },
                { leftScale := 295334641809, quotient := Hex.DensePoly.ofCoeffs #[-93737160, 709198335],
                  rightScale := 60552 },
                { leftScale := 76870081016350350481,
                  quotient := Hex.DensePoly.ofCoeffs #[-13112906159071696, 4764703332086127],
                  rightScale := 13290058881405 },
                { leftScale := 40708697215950389749844484,
                  quotient := Hex.DensePoly.ofCoeffs #[24826723697280497242096, 55939975447439931989202],
                  rightScale := 2613582754555911916354 },
                { leftScale := 112467437043324348106552305625,
                  quotient := Hex.DensePoly.ofCoeffs #[3870888879752767371158325616, 2139720271729614105228948150],
                  rightScale := 105645407999871253676067 },
                { leftScale := 38226743133961988387999266173523827961,
                  quotient :=
                    Hex.DensePoly.ofCoeffs #[-5893169277272969403976213446164168, 2073466620611530658632835068046825],
                  rightScale := 15295571437892111342491113565000 },
                { leftScale := 5216268710940777301984547673654804283969,
                  quotient :=
                    Hex.DensePoly.ofCoeffs
                      #[907712564018517562947592483669178879958, 446543350785627655198222290095524042453],
                  rightScale := 152906972535847953551997064694095311844 },
                { leftScale := 263299611058233386804649790651598647549249,
                  quotient :=
                    Hex.DensePoly.ofCoeffs
                      #[25339344713332469479224464649579883249982, 37059971974705257474716159594930990870591],
                  rightScale := 90040977060176571371062804618034212674422203392 },
                { leftScale := 94033677189418726887312988401,
                  quotient :=
                    Hex.DensePoly.ofCoeffs
                      #[-378302466721854007725727909006194872, 157350025835235958508302235093612793],
                  rightScale := 43822481669465531377774718431581132835375944263449 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-51) >>> 4, upper := Dyadic.ofInt (-203) >>> 6, lt := by decide },
            { lower := Dyadic.ofInt (-101) >>> 5, upper := Dyadic.ofInt (-201) >>> 6, lt := by decide },
            { lower := Dyadic.ofInt (-25) >>> 3, upper := Dyadic.ofInt (-3), lt := by decide },
            { lower := Dyadic.ofInt (-23) >>> 6, upper := Dyadic.ofInt (-11) >>> 5, lt := by decide },
            { lower := Dyadic.ofInt (-21) >>> 6, upper := Dyadic.ofInt (-5) >>> 4, lt := by decide },
            { lower := Dyadic.ofInt 5 >>> 4, upper := Dyadic.ofInt 21 >>> 6, lt := by decide },
            { lower := Dyadic.ofInt 11 >>> 5, upper := Dyadic.ofInt 23 >>> 6, lt := by decide },
            { lower := Dyadic.ofInt 2, upper := Dyadic.ofInt 3, lt := by decide },
            { lower := Dyadic.ofInt 201 >>> 6, upper := Dyadic.ofInt 101 >>> 5, lt := by decide },
            { lower := Dyadic.ofInt 203 >>> 6, upper := Dyadic.ofInt 51 >>> 4, lt := by decide },
            { lower := Dyadic.ofInt 7 >>> 1, upper := Dyadic.ofInt 4, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[576, -144, -4852, 1213, 1000, -250, -52, 13],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[1, 0, -10, 0, 1], Hex.DensePoly.ofCoeffs #[0, -5, 0, 1],
                        Hex.DensePoly.ofCoeffs #[-1, 0, 5], Hex.DensePoly.ofCoeffs #[0, 1],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 4,
                    steps :=
                      #[{ leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 1 },
                        { leftScale := 5, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 24 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 5], rightScale := 1 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-3, 1], atomFactor := Hex.DensePoly.ofCoeffs #[-1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-192, -16, 3532, 293, -16601, -1359, 4515, 263, -419, -13, 13],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := -1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-3, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-4, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-144, 0, 2653, 0, -12524, 0, 3726, 0, -380, 0, 13],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-4, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-144, 0, 1213, 0, -250, 0, 13],
              atomFactor := Hex.DensePoly.ofCoeffs #[-1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-4, 1, 40, -10, -4, 1],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := -1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-144, 0, 1213, 0, -250, 0, 13],
                        Hex.DensePoly.ofCoeffs #[0, 1213, 0, -500, 0, 39],
                        Hex.DensePoly.ofCoeffs #[216, 0, -1213, 0, 125], Hex.DensePoly.ofCoeffs #[0, -143201, 0, 15193],
                        Hex.DensePoly.ofCoeffs #[-15193, 0, 2449], Hex.DensePoly.ofCoeffs #[0, 1],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 2,
                    steps :=
                      #[{ leftScale := 39, quotient := Hex.DensePoly.ofCoeffs #[0, 13], rightScale := 26 },
                        { leftScale := 125, quotient := Hex.DensePoly.ofCoeffs #[0, 39], rightScale := 1 },
                        { leftScale := 15193, quotient := Hex.DensePoly.ofCoeffs #[0, 125], rightScale := 216 },
                        { leftScale := 2449, quotient := Hex.DensePoly.ofCoeffs #[0, 15193], rightScale := 119872000 },
                        { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 2449], rightScale := 15193 }] } }] },
    iocCmps := Option.none })

syntax "cadTower4Input" : term
macro_rules
  | `(cadTower4Input) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 1], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-1, 1], cmp := Hex.RCF.Cmp.gt }).imp
      (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[0, 1, -1], cmp := Hex.RCF.Cmp.lt }))))

syntax "cadTower4Cert" : term
macro_rules
  | `(cadTower4Cert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[0, 2, -2, 0, 0, -1, 1], repeated := Hex.DensePoly.ofCoeffs #[-1, 1],
        derivPart := Hex.DensePoly.ofCoeffs #[-2, 6, 0, 0, 5, -7], factorScale := -1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[0, 2, -2, 0, 0, -1, 1], Hex.DensePoly.ofCoeffs #[2, -4, 0, 0, -5, 6],
                Hex.DensePoly.ofCoeffs #[-2, -56, 48, 0, 5], Hex.DensePoly.ofCoeffs #[0, 1, -2, 1],
                Hex.DensePoly.ofCoeffs #[2, 66, -63], Hex.DensePoly.ofCoeffs #[8, -9], Hex.DensePoly.ofCoeffs #[-1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 36, quotient := Hex.DensePoly.ofCoeffs #[-1, 6], rightScale := 1 },
                { leftScale := 25, quotient := Hex.DensePoly.ofCoeffs #[-25, 30], rightScale := 1440 },
                { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[10, 5], rightScale := 1 },
                { leftScale := 3969, quotient := Hex.DensePoly.ofCoeffs #[60, -63], rightScale := 15 },
                { leftScale := 81, quotient := Hex.DensePoly.ofCoeffs #[-90, 567], rightScale := 882 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-3) >>> 1, upper := Dyadic.ofInt (-1), lt := by decide },
            { lower := Dyadic.ofInt (-1) >>> 2, upper := Dyadic.ofInt 0, lt := by decide },
            { lower := Dyadic.ofInt 15 >>> 4, upper := Dyadic.ofInt 1, lt := by decide },
            { lower := Dyadic.ofInt 9 >>> 3, upper := Dyadic.ofInt 5 >>> 2, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -1, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 1], Hex.DensePoly.ofCoeffs #[0, 0, 0, 1],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 4,
                    steps := #[{ leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 2 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -2, 0, 0, 0, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-1, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[0, -1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[-1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := -1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[0, -1, 1], Hex.DensePoly.ofCoeffs #[-1, 2],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 1,
                    steps := #[{ leftScale := 4, quotient := Hex.DensePoly.ofCoeffs #[-1, 2], rightScale := 1 }] } }] },
    iocCmps := Option.none })

syntax "cadTower8Input" : term
macro_rules
  | `(cadTower8Input) => `(Hex.RCF.Sentence.forallReal
  ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 0, 0, 0, 0, 1], cmp := Hex.RCF.Cmp.eq }).imp
    ((Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[-1, 1], cmp := Hex.RCF.Cmp.gt }).imp
      (Hex.RCF.Formula.atom { p := Hex.DensePoly.ofCoeffs #[0, 1, -1], cmp := Hex.RCF.Cmp.lt }))))

syntax "cadTower8Cert" : term
macro_rules
  | `(cadTower8Cert) => `(Hex.RCF.Certificate.cells
  {
    carrier :=
      { carrier := Hex.DensePoly.ofCoeffs #[0, 2, -2, 0, 0, 0, 0, 0, 0, -1, 1],
        repeated := Hex.DensePoly.ofCoeffs #[-1, 1],
        derivPart := Hex.DensePoly.ofCoeffs #[-2, 6, 0, 0, 0, 0, 0, 0, 9, -11], factorScale := -1, derivScale := 1,
        replay :=
          {
            chain :=
              #[Hex.DensePoly.ofCoeffs #[0, 2, -2, 0, 0, 0, 0, 0, 0, -1, 1],
                Hex.DensePoly.ofCoeffs #[2, -4, 0, 0, 0, 0, 0, 0, -9, 10],
                Hex.DensePoly.ofCoeffs #[-2, -176, 160, 0, 0, 0, 0, 0, 9], Hex.DensePoly.ofCoeffs #[0, 1, -2, 1],
                Hex.DensePoly.ofCoeffs #[2, 230, -223], Hex.DensePoly.ofCoeffs #[48, -55],
                Hex.DensePoly.ofCoeffs #[-1]],
            derivScale := 1,
            steps :=
              #[{ leftScale := 100, quotient := Hex.DensePoly.ofCoeffs #[-1, 10], rightScale := 1 },
                { leftScale := 81, quotient := Hex.DensePoly.ofCoeffs #[-81, 90], rightScale := 14400 },
                { leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[54, 45, 36, 27, 18, 9], rightScale := 1 },
                { leftScale := 49729, quotient := Hex.DensePoly.ofCoeffs #[216, -223], rightScale := 9 },
                { leftScale := 3025, quotient := Hex.DensePoly.ofCoeffs #[-1946, 12265], rightScale := 99458 }] } },
    isolations :=
      {
        intervals :=
          #[{ lower := Dyadic.ofInt (-3) >>> 1, upper := Dyadic.ofInt (-1), lt := by decide },
            { lower := Dyadic.ofInt (-1) >>> 2, upper := Dyadic.ofInt 0, lt := by decide },
            { lower := Dyadic.ofInt 31 >>> 5, upper := Dyadic.ofInt 1, lt := by decide },
            { lower := Dyadic.ofInt 17 >>> 4, upper := Dyadic.ofInt 9 >>> 3, lt := by decide }] },
    signs :=
      {
        commonRoots :=
          [{ gcd := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 0, 0, 0, 0, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -1, 1], atomCoeff := Hex.DensePoly.ofCoeffs #[1],
              carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 0, 0, 0, 0, 1],
                        Hex.DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, 0, 1], Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 8,
                    steps := #[{ leftScale := 1, quotient := Hex.DensePoly.ofCoeffs #[0, 1], rightScale := 2 }] } },
            { gcd := Hex.DensePoly.ofCoeffs #[-1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[0, -2, 0, 0, 0, 0, 0, 0, 0, 1],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := 1,
              replay :=
                Option.some
                  { chain := #[Hex.DensePoly.ofCoeffs #[-1, 1], Hex.DensePoly.ofCoeffs #[1]], derivScale := 1,
                    steps := #[] } },
            { gcd := Hex.DensePoly.ofCoeffs #[0, -1, 1], atomFactor := Hex.DensePoly.ofCoeffs #[-1],
              carrierFactor := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 0, 0, 0, 0, 1],
              atomCoeff := Hex.DensePoly.ofCoeffs #[1], carrierCoeff := Hex.DensePoly.ofCoeffs #[], scale := -1,
              replay :=
                Option.some
                  {
                    chain :=
                      #[Hex.DensePoly.ofCoeffs #[0, -1, 1], Hex.DensePoly.ofCoeffs #[-1, 2],
                        Hex.DensePoly.ofCoeffs #[1]],
                    derivScale := 1,
                    steps := #[{ leftScale := 4, quotient := Hex.DensePoly.ofCoeffs #[-1, 2], rightScale := 1 }] } }] },
    iocCmps := Option.none })

