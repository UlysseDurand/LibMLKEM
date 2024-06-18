package body RefMLKEM 
    with SPARK_Mode => On
is
   function NTT_Ref (A : in Poly_Zq_Ref) return NTT_Poly_Zq_Ref
   is
      A_HAT : NTT_Poly_Zq_Ref;
   begin
      for I in Index_Ref'Range loop
         declare
            Array_To_Sum : Array_Zq (Index_Ref'Range);
         begin
            for J in Index_Ref loop
               Array_To_Sum (J) := (Psi ** (2 * To_Big (I) * To_Big (J) + To_Big (I) ) * A (I));
            end loop;
            A_HAT (I) := Generic_Sum.Sum (Array_To_Sum);
         end;
      end loop;
      return A_HAT;
   end NTT_Ref;
end RefMLKEM;

