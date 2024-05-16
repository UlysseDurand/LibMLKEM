--  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
--  SPDX-License-Identifier: Apache-2.0

with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

with Interfaces; use Interfaces;
package MLKEM
  with SPARK_Mode => On
is

   --  Our lemmas for the SPARK proof

   -- Prove a number is prime

   --  function givesBigInterval (A : Big_Integer ; B : Big_Integer) return Interval with
   --     Post => (for all X in givesBigIntervalBasic (A, B) => In_Range(givesBigInterval(A, B), X)); 

   --  function Is_Prime (N : Big_Natural) return Boolean is
   --  (for all J in givesBigInterval(2,N) => ( N mod J /= 0));

   --  procedure Number_Is_Prime (N : Big_Natural)
   --  with
   --     Ghost,
   --     Global => null,
   --     Post => Is_Prime(N);

   function obviousComp(A : Big_Integer; B : Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0,
      Post => A/B <= abs A;


   -- Correspondance between definitions of one number divides another
   function CorrespDividOne(A : Big_Integer; B : Big_Integer) return Big_Integer with
      Ghost,
      Pre => B /= 0 and then (A mod B = 0),
      Post =>  
         In_Range(Interval'(-abs A, abs A), CorrespDividOne'Result) and 
         (A = CorrespDividOne'Result * B);

   function CorrespDividTwo(A : Big_Integer; B : Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0 and then (for some k in Interval'(-abs A, abs A) => (A = k * B)),
      Post => CorrespDividTwo'Result and A mod B = 0;
  
   --  if B divides A then B divides A * M
   function goodDivideMult(A : Big_Integer; B : Big_Integer; M : Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0 and then(A mod B = 0),
      Post => A * M mod B = 0;

   function goodDivideAdd(B: Big_Integer; C: Big_Integer; D: Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0 and then(C mod B = 0 and D mod B =0),
      Post => (C + D) mod B = 0;

   type Ext_cd is record 
      U : Big_Integer;
      V : Big_Integer;
      D : Big_Natural;
   end Record;

   function ext_gcd (A : Big_Natural; B : Big_Natural) return Ext_cd
   with
      Ghost,
      Annotate => (GNATprove, Always_Return),
      Subprogram_Variant => (Decreases => B),
      Pre => B /= 0,
      Post =>
         ext_gcd'Result.D > 0 and
         A * ext_gcd'Result.U + B * ext_gcD'Result.V = ext_gcd'Result.D and
         A mod ext_gcd'Result.D = 0 and
         B mod ext_gcd'Result.D = 0;



   --  function Lemma_prime_divides_product
   --     (A : Big_Natural ;
   --     B : Big_Natural ;
   --     P : Big_Natural )
   --  return Boolean with
   --     Ghost,
   --     Global=>null,
   --     Pre=>
   --        Is_Prime(P) and
   --        (A * B) mod P = 0,
   --     Post =>
   --        A mod P = 0 or 
   --        B mod P = 0
   --        ;
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
      --  In theory, Zq could fit in 12 bits, but we force compiler to
      --  represent it in 16 bits for natural convenience and efficiency
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
   end Zq;

end MLKEM;
