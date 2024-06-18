package body RefMLKEM 
    with SPARK_Mode => On
is

   type Variabla_Length_Poly_Zq is array (Index_Ref range <>) of T_Ref;

   package The_Sum_NTT_Poly_Zq is new SumGen.Sum_On_Array (T_Ref, Index_Ref, Variabla_Length_Poly_Zq);

   function NTT_Ref (A : in Poly_Zq_Ref) return NTT_Poly_Zq_Ref
   is
      A_HAT : NTT_Poly_Zq_Ref;
   begin
      for I in Index_Ref'Range loop
         declare
            function Sum_Expression (J : Index_Ref) return T_Ref is
               (Psi ** (2 * To_Big (I) * To_Big (J) + To_Big (I) ) * A (I));
            function Sum_Array_Generator is new The_Sum_NTT_Poly_Zq.InitialArray (Sum_Expression);
            Array_To_Sum : Variabla_Length_Poly_Zq (0 .. Index_Ref'Last) := Sum_Array_Generator (Integer (Index_Ref'Last) + 1);
            package Lemma_Split is new The_Sum_NTT_Poly_Zq.Generic_Lemma_Split_Sum_Func_Odd_Even (Sum_Expression); 
         begin
            A_HAT (I) := The_Sum_NTT_Poly_Zq.Sum (Array_To_Sum);
         end;
      end loop;
      return A_HAT;
   end NTT_Ref;

end RefMLKEM;