--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with Interfaces; use Interfaces;
with SPARK.Big_Integers; use SPARK.Big_Integers;
package MLKEM
  with SPARK_Mode => On
is
   --==============================================
   --  Exported constants, types, and subprograms
   --
   --  These are needed by clients, or by the
   --  specifications of child packages
   --==============================================

   --  Constants common to all parameter sets
   --  from FIPS 203 section 7
   Q      : constant := 3329;
   N      : constant := 256;
   N_INV  : constant := 3277;

   ----------------------------------------------------------------------
   --  TODO - make the entire package generic over these parameter values
   ----------------------------------------------------------------------

   --  Parameters for ML-KEM-512 from FIPS 203 section 7
   --  K      : constant := 2;
   --  Eta_1  : constant := 3;
   --  Eta_2  : constant := 2;
   --  DU     : constant := 10;
   --  DV     : constant := 4;

   --  Parameters for ML-KEM-768 from FIPS 203 section 7
   K      : constant := 3;
   Eta_1  : constant := 2;
   Eta_2  : constant := 2;
   DU     : constant := 10;
   DV     : constant := 4;

   --  Parameters for ML-KEM-1024 from FIPS 203 section 7
   --  K      : constant := 4;
   --  Eta_1  : constant := 2;
   --  Eta_2  : constant := 2;
   --  DU     : constant := 11;
   --  DV     : constant := 5;

   ----------------------------------------------------------------------
   --  Parameter set validation
   ----------------------------------------------------------------------

   --  FIPS 203 section 6 requires that implementations shall confirm
   --  that only valid sets of parameters are chosen.  This can be
   --  encoded as an assertion, thus:
   pragma Assert
      --  ML-KEM-512
      ((K = 2 and Eta_1 = 3 and Eta_2 = 2 and DU = 10 and DV = 4) or
       --  ML-KEM-768
       (K = 3 and Eta_1 = 2 and Eta_2 = 2 and DU = 10 and DV = 4) or
       --  ML-KEM-1024
       (K = 4 and Eta_1 = 2 and Eta_2 = 2 and DU = 11 and DV = 5));


   subtype Byte is Unsigned_8;
   subtype I32  is Integer_32;
   subtype N32  is I32 range 0 .. I32'Last;

   subtype Index_256 is I32 range 0 .. 255;

   --  Unconstrained (aka "Size Polymorphic") array of bytes
   type Byte_Seq is array (N32 range <>) of Byte;

   subtype Index_32  is I32 range 0 .. 31;
   subtype Bytes_32  is Byte_Seq (Index_32);

   --  Ciphertext is 1088 bytes for K = 3, DU = 10, DV = 4
   subtype Ciphertext_Index is I32 range 0 .. 32 * (DU * K + DV) - 1;
   subtype Ciphertext is Byte_Seq (Ciphertext_Index);

   --  1184 bytes for K = 3
   subtype MLKEM_Encapsulation_Key_Index is I32 range 0 .. (384 * K + 32 - 1);
   subtype MLKEM_Encapsulation_Key is Byte_Seq (MLKEM_Encapsulation_Key_Index);

   --  2400 bytes for K = 3
   subtype MLKEM_Decapsulation_Key_Index is I32 range 0 .. (768 * K + 96 - 1);
   subtype MLKEM_Decapsulation_Key is Byte_Seq (MLKEM_Decapsulation_Key_Index);

   type MLKEM_Key is record
      EK : MLKEM_Encapsulation_Key;
      DK : MLKEM_Decapsulation_Key;
   end record;

   --==============================================
   --  Exported subprograms. These 4 subprograms
   --  form the main user-facing API for MLKEM
   --==============================================

   --  Input data validation for Algorithm 16. FIPS 203 line 984
   function EK_Is_Valid_For_Encaps (EK : in MLKEM_Encapsulation_Key)
     return Boolean
     with Global => null;

   --  Algorithm 15
   function MLKEM_KeyGen (Random_D : in Bytes_32;
                          Random_Z : in Bytes_32) return MLKEM_Key
     with Global => null;

   --  Algorithm 16
   procedure MLKEM_Encaps (EK       : in     MLKEM_Encapsulation_Key;
                           Random_M : in     Bytes_32;
                           SS       :    out Bytes_32;
                           C        :    out Ciphertext)
     with Global => null,
                     --  Precondition from FIPS 203 lines 980 - 985
          Pre    => EK'Length = 384 * K + 32 and
                    EK_Is_Valid_For_Encaps (EK);

   --  Algorithm 17
   function MLKEM_Decaps (C  : in Ciphertext;
                          DK : in MLKEM_Decapsulation_Key) return Bytes_32
     with Global => null,
                     --  Precondition from FIPS 203 lines 1009 - 1014
          Pre    => C'Length = 32 * (DU * K + DV) and
                    DK'Length = 768 * K + 96;
private
   subtype U16 is Unsigned_16;
   subtype U32 is Unsigned_32;
   subtype U64 is Unsigned_64;
   subtype I64 is Integer_64;

   --  FIPS 203, 2.3, line 414
   subtype SU7 is Byte range 0 .. 127;

   subtype Index_128 is I32 range 0 .. 127;

   --  We wrap type Zq.T in its own package so we can precisely control
   --  which operators ("+", "-", "*" etc) are available for it, and how
   --  they are implemented.
   --
   --  This package is declared here, so it is visible to the public
   --  child package MLKEM.Tests
   package Zq
     with SPARK_Mode => On
   is
      --  In theory, Zq could fit in 12 bits, but force compiler
      --  to represent in 16 bits for natural convenience and efficiency
      type T is mod Q
        with Object_Size => 16;

      subtype Zq_Bit is T range 0 .. 1;

      --  OVERRIDE the opertors that we wish to allow for T, but
      --  to allow for implementations which are specific to a particular
      --  CPU and/or constant-time at all optimization levels.
      function "+" (Left, Right : in T) return T
         with No_Inline,
              Global => null,
              Post => "+"'Result = T ((I32 (Left) + I32 (Right)) mod Q);

      function "-" (Left, Right : in T) return T
         with No_Inline,
              Global => null,
              Post => "-"'Result = T ((I32 (Left) - I32 (Right)) mod Q);

      function "*" (Left, Right : in T) return T
         with No_Inline,
              Global => null,
              Post => "*"'Result = T ((I64 (Left) * I64 (Right)) mod Q);

      --  Divide "Right" by 2
      function Div2 (Right : in T) return T
         with Inline_Always,
              Global => null;

      --  Returns X mod Q, but implemented in constant time.
      function ModQ (X : in U16) return T
         with No_Inline,
              Global => null,
              Post   => ModQ'Result = T (X mod Q);

      --  Returns the inverse if Zq, only used in proof and specification
      --  so it has the Ghost flag and constant time isn't needed      
      --  function Inverse (A : T) return T
      --     with Ghost,
      --          Pre => A /= 0,
      --          Post => A * Inverse'Result = 1;

      --  Returns A ** B, only used in proof and specification
      --  so it has the Ghost flag and constant time isn't needed
      function "**" (A : T;
                     B : Big_Natural) return T;

      type Zq_Function_Access is not null access function (X : Index_256) return T;

      type K_Range is range 0 .. K - 1;

      type Poly_Zq is array (Index_256) of Zq.T;

      type Poly_Zq_Vector is array (K_Range) of Poly_Zq;

      --  Polynomials in the NTT domain are structurally identical to the
      --  above, but should never be mixed up with them, so we declare
      --  an explicitly derived named types for them here.
      type NTT_Poly_Zq is new Poly_Zq;
      type NTT_Poly_Zq_Vector is array (K_Range) of NTT_Poly_Zq;
      type NTT_Poly_Matrix    is array (K_Range) of NTT_Poly_Zq_Vector;

      generic
         with function Func (P1     : Poly_Zq;
                             P2     : Index_256; 
                             J      : Index_256) return T;
      function Sum_Parametrized    (A : Index_256;
                                    B : Index_256; 
                                    P1: Poly_Zq;
                                    P2 : Index_256) return T;

      generic
         with function Func_NTT (P1    : NTT_Poly_Zq;
                                 P2    : Index_256; 
                                 I     : Index_256) return T;
      function Sum_Parametrized_NTT(A : Index_256;
                                    B : Index_256; 
                                    P1: NTT_Poly_Zq;
                                    P2 : Index_256) return T;


      --  Forbid all other predefined operators on T
      function "+"   (Right : in T) return T is abstract;
      function "-"   (Right : in T) return T is abstract;
      function "abs" (Right : in T) return T is abstract;
      function "/"   (Left, Right : in T) return T is abstract;
      function "mod" (Left, Right : in T) return T is abstract;
      function "rem" (Left, Right : in T) return T is abstract;
      function "**"  (Left : in T; Right : in Natural) return T is abstract;

      --  Stop the compiler warning about unreferenced entities
      pragma Unreferenced ("+");
      pragma Unreferenced ("-");
      pragma Unreferenced ("abs");
      pragma Unreferenced ("/");
      pragma Unreferenced ("mod");
      pragma Unreferenced ("rem");

      Zeta : constant T := 17;
      Zeta_Inv : constant T := 1175;

   end Zq;


end MLKEM;
