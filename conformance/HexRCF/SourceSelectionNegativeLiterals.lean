/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec
public section
namespace Hex.RCF.RealCoefficients.SourceSelectionNegativeLiterals
open Hex.SignDet
/-! Frozen native proposal for the negative root of X²−2 in (-3/2,-7/5).
The consuming module quotes the exact literal reader in the ordinary kernel. -/
@[expose] def subject : Codec.Json :=
.array
  (.cons
    (.number 8)
    (.cons
      (.array
        (.cons
          (.array
            (.cons
              (.number (-2))
              (.cons
                (.number 1)
                (.nil))))
          (.cons
            (.array
              (.cons
                (.number 0)
                (.cons
                  (.number 1)
                  (.nil))))
            (.cons
              (.array
                (.cons
                  (.number 1)
                  (.cons
                    (.number 1)
                    (.nil))))
              (.nil)))))
      (.cons
        (.array
          (.cons
            (.number 1)
            (.cons
              (.array
                (.cons
                  (.number (-3))
                  (.cons
                    (.number 2)
                    (.nil))))
              (.nil))))
        (.cons
          (.array
            (.cons
              (.number 1)
              (.cons
                (.array
                  (.cons
                    (.number (-7))
                    (.cons
                      (.number 5)
                      (.nil))))
                (.nil))))
          (.cons
            (.array (.nil))
            (.cons
              (.array (.nil))
              (.nil)))))))

@[expose] def graph : Codec.Json :=
.array
  (.cons
    (.number 1)
    (.cons
      (.number 0)
      (.cons
        (.array
          (.cons
            (.array
              (.cons
                (.array
                  (.cons
                    (.number 8)
                    (.cons
                      (.array
                        (.cons
                          (.array
                            (.cons
                              (.number (-2))
                              (.cons
                                (.number 1)
                                (.nil))))
                          (.cons
                            (.array
                              (.cons
                                (.number 0)
                                (.cons
                                  (.number 1)
                                  (.nil))))
                            (.cons
                              (.array
                                (.cons
                                  (.number 1)
                                  (.cons
                                    (.number 1)
                                    (.nil))))
                              (.nil)))))
                      (.cons
                        (.array
                          (.cons
                            (.number 1)
                            (.cons
                              (.array
                                (.cons
                                  (.number (-3))
                                  (.cons
                                    (.number 2)
                                    (.nil))))
                              (.nil))))
                        (.cons
                          (.array
                            (.cons
                              (.number 1)
                              (.cons
                                (.array
                                  (.cons
                                    (.number (-7))
                                    (.cons
                                      (.number 5)
                                      (.nil))))
                                (.nil))))
                          (.cons
                            (.array (.nil))
                            (.cons
                              (.number 1)
                              (.cons
                                (.array
                                  (.cons
                                    (.array
                                      (.cons
                                        (.array (.nil))
                                        (.nil)))
                                    (.cons
                                      (.array
                                        (.cons
                                          (.array (.nil))
                                          (.nil)))
                                      (.cons
                                        (.array
                                          (.cons
                                            (.number 1)
                                            (.nil)))
                                        (.cons
                                          (.array
                                            (.cons
                                              (.number 1)
                                              (.nil)))
                                          (.cons
                                            (.array
                                              (.cons
                                                (.array
                                                  (.cons
                                                    (.number 1)
                                                    (.nil)))
                                                (.nil)))
                                            (.cons
                                              (.number 1)
                                              (.nil))))))))
                                (.cons
                                  (.array
                                    (.cons
                                      (.array
                                        (.cons
                                          (.number 8)
                                          (.cons
                                            (.array
                                              (.cons
                                                (.array
                                                  (.cons
                                                    (.number (-2))
                                                    (.cons
                                                      (.number 1)
                                                      (.nil))))
                                                (.cons
                                                  (.array
                                                    (.cons
                                                      (.number 0)
                                                      (.cons
                                                        (.number 1)
                                                        (.nil))))
                                                  (.cons
                                                    (.array
                                                      (.cons
                                                        (.number 1)
                                                        (.cons
                                                          (.number 1)
                                                          (.nil))))
                                                    (.nil)))))
                                            (.cons
                                              (.array
                                                (.cons
                                                  (.array
                                                    (.cons
                                                      (.number 1)
                                                      (.cons
                                                        (.number 1)
                                                        (.nil))))
                                                  (.nil)))
                                              (.cons
                                                (.array
                                                  (.cons
                                                    (.number 1)
                                                    (.cons
                                                      (.array
                                                        (.cons
                                                          (.number (-3))
                                                          (.cons
                                                            (.number 2)
                                                            (.nil))))
                                                      (.nil))))
                                                (.cons
                                                  (.array
                                                    (.cons
                                                      (.number 1)
                                                      (.cons
                                                        (.array
                                                          (.cons
                                                            (.number (-7))
                                                            (.cons
                                                              (.number 5)
                                                              (.nil))))
                                                        (.nil))))
                                                  (.cons
                                                    (.array
                                                      (.cons
                                                        (.array
                                                          (.cons
                                                            (.array
                                                              (.cons
                                                                (.array
                                                                  (.cons
                                                                    (.number (-2))
                                                                    (.cons
                                                                      (.number 1)
                                                                      (.nil))))
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.number 0)
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.nil))))
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.nil))))
                                                                    (.nil)))))
                                                            (.cons
                                                              (.array
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.number 0)
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.nil))))
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.nil))))
                                                                    (.nil))))
                                                              (.cons
                                                                (.array
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.nil))))
                                                                    (.nil)))
                                                                (.nil)))))
                                                        (.cons
                                                          (.array
                                                            (.cons
                                                              (.number 2)
                                                              (.cons
                                                                (.number 1)
                                                                (.cons
                                                                  (.number 0)
                                                                  (.nil)))))
                                                          (.cons
                                                            (.array
                                                              (.cons
                                                                (.array
                                                                  (.cons
                                                                    (.number 1)
                                                                    (.cons
                                                                      (.number 1)
                                                                      (.nil))))
                                                                (.cons
                                                                  (.array
                                                                    (.nil))
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.number 2)
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.nil))))
                                                                    (.nil)))))
                                                            (.cons
                                                              (.array
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.array
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.nil))))
                                                                      (.cons
                                                                        (.array
                                                                          (.cons
                                                                            (.array
                                                                              (.cons
                                                                                (.number 0)
                                                                                (.cons
                                                                                  (.number
                                                                                    1)
                                                                                  (.nil))))
                                                                            (.cons
                                                                              (.array
                                                                                (.cons
                                                                                  (.number
                                                                                    1)
                                                                                  (.cons
                                                                                    (.number
                                                                                      1)
                                                                                    (.nil))))
                                                                              (.nil))))
                                                                        (.cons
                                                                          (.array
                                                                            (.cons
                                                                              (.number 2)
                                                                              (.cons
                                                                                (.number 1)
                                                                                (.nil))))
                                                                          (.nil)))))
                                                                  (.nil)))
                                                              (.cons
                                                                (.array
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.array
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.cons
                                                                              (.number 1)
                                                                              (.nil))))
                                                                        (.cons
                                                                          (.array
                                                                            (.cons
                                                                              (.array
                                                                                (.cons
                                                                                  (.number
                                                                                    0)
                                                                                  (.cons
                                                                                    (.number
                                                                                      1)
                                                                                    (.nil))))
                                                                              (.cons
                                                                                (.array
                                                                                  (.cons
                                                                                    (.number
                                                                                      1)
                                                                                    (.cons
                                                                                      (.number
                                                                                        1)
                                                                                      (.nil))))
                                                                                (.nil))))
                                                                          (.nil))))
                                                                    (.nil)))
                                                                (.nil)))))))
                                                    (.cons
                                                      (.array
                                                        (.cons
                                                          (.array
                                                            (.cons
                                                              (.array
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.number (-2))
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.nil))))
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.number 0)
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.nil))))
                                                                    (.cons
                                                                      (.array
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.nil))))
                                                                      (.nil)))))
                                                              (.cons
                                                                (.array
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.number 0)
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.nil))))
                                                                    (.cons
                                                                      (.array
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.nil))))
                                                                      (.nil))))
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.array
                                                                        (.cons
                                                                          (.number 1)
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.nil))))
                                                                      (.nil)))
                                                                  (.nil)))))
                                                          (.cons
                                                            (.array
                                                              (.cons
                                                                (.number 2)
                                                                (.cons
                                                                  (.number 1)
                                                                  (.cons
                                                                    (.number 0)
                                                                    (.nil)))))
                                                            (.cons
                                                              (.array
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.number 1)
                                                                      (.cons
                                                                        (.number 1)
                                                                        (.nil))))
                                                                  (.cons
                                                                    (.array
                                                                      (.nil))
                                                                    (.cons
                                                                      (.array
                                                                        (.cons
                                                                          (.number 2)
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.nil))))
                                                                      (.nil)))))
                                                              (.cons
                                                                (.array
                                                                  (.cons
                                                                    (.array
                                                                      (.cons
                                                                        (.array
                                                                          (.cons
                                                                            (.number 1)
                                                                            (.cons
                                                                              (.number 1)
                                                                              (.nil))))
                                                                        (.cons
                                                                          (.array
                                                                            (.cons
                                                                              (.array
                                                                                (.cons
                                                                                  (.number
                                                                                    0)
                                                                                  (.cons
                                                                                    (.number
                                                                                      1)
                                                                                    (.nil))))
                                                                              (.cons
                                                                                (.array
                                                                                  (.cons
                                                                                    (.number
                                                                                      1)
                                                                                    (.cons
                                                                                      (.number
                                                                                        1)
                                                                                      (.nil))))
                                                                                (.nil))))
                                                                          (.cons
                                                                            (.array
                                                                              (.cons
                                                                                (.number 2)
                                                                                (.cons
                                                                                  (.number
                                                                                    1)
                                                                                  (.nil))))
                                                                            (.nil)))))
                                                                    (.nil)))
                                                                (.cons
                                                                  (.array
                                                                    (.cons
                                                                      (.array
                                                                        (.cons
                                                                          (.array
                                                                            (.cons
                                                                              (.number 1)
                                                                              (.cons
                                                                                (.number 1)
                                                                                (.nil))))
                                                                          (.cons
                                                                            (.array
                                                                              (.cons
                                                                                (.array
                                                                                  (.cons
                                                                                    (.number
                                                                                      0)
                                                                                    (.cons
                                                                                      (.number
                                                                                        1)
                                                                                      (.nil))))
                                                                                (.cons
                                                                                  (.array
                                                                                    (.cons
                                                                                      (.number
                                                                                        1)
                                                                                      (.cons
                                                                                        (.number
                                                                                          1)
                                                                                        (.nil))))
                                                                                  (.nil))))
                                                                            (.nil))))
                                                                      (.nil)))
                                                                  (.nil)))))))
                                                      (.cons
                                                        (.array
                                                          (.cons
                                                            (.number 1)
                                                            (.cons
                                                              (.number (-1))
                                                              (.cons
                                                                (.number 1)
                                                                (.nil)))))
                                                        (.cons
                                                          (.array
                                                            (.cons
                                                              (.number (-1))
                                                              (.cons
                                                                (.number (-1))
                                                                (.cons
                                                                  (.number 1)
                                                                  (.nil)))))
                                                          (.cons
                                                            (.number 2)
                                                            (.cons
                                                              (.number 1)
                                                              (.cons
                                                                (.number 1)
                                                                (.nil))))))))))))))
                                      (.nil)))
                                  (.cons
                                    (.array
                                      (.cons
                                        (.array
                                          (.cons
                                            (.array
                                              (.cons
                                                (.array (.nil))
                                                (.cons
                                                  (.array
                                                    (.cons
                                                      (.array
                                                        (.cons
                                                          (.number 1)
                                                          (.cons
                                                            (.number 1)
                                                            (.nil))))
                                                      (.nil)))
                                                  (.nil))))
                                            (.nil)))
                                        (.nil)))
                                    (.cons
                                      (.array
                                        (.cons
                                          (.array (.nil))
                                          (.nil)))
                                      (.cons
                                        (.array
                                          (.cons
                                            (.number 1)
                                            (.cons
                                              (.array
                                                (.cons
                                                  (.number 0)
                                                  (.nil)))
                                              (.cons
                                                (.array
                                                  (.cons
                                                    (.number 0)
                                                    (.nil)))
                                                (.cons
                                                  (.number 1)
                                                  (.cons
                                                    (.array
                                                      (.cons
                                                        (.array
                                                          (.cons
                                                            (.number 1)
                                                            (.nil)))
                                                        (.nil)))
                                                    (.nil)))))))
                                        (.nil)))))))))))))
                (.cons
                  (.array (.nil))
                  (.nil))))
            (.nil)))
        (.nil))))
end Hex.RCF.RealCoefficients.SourceSelectionNegativeLiterals
