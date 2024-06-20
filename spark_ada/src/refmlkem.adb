
package body RefMLKEM 
    with SPARK_Mode => On
is
--  Length has to be equal to Integer (Index256'Last) + 1 in function calls.
--  Psi has to be equal to a 256 primary root of the unity like 17.
function NTT_Ref (E : Array_Zq;
                  Psi : T_Ref) return Array_Zq
   is
      E_HAT : Array_Zq (E'Range) with Relaxed_Initialization;
   begin
      for I in E'Range loop
         declare
            Array_To_Sum : Array_Zq (E'Range) with Relaxed_Initialization;
         begin
            for J in E'Range loop
               Array_To_Sum (J) := (Psi ** (2 * To_Big (I) * To_Big (J) + To_Big (I) ) * E (I));
               pragma Loop_Invariant (for all K in E'First .. J => Array_To_Sum (K)'Initialized);
            end loop;
            E_HAT (I) := Generic_Sum.Sum (Array_To_Sum);
            pragma Assume (for all K in E'First .. I => E_HAT (K)'Initialized);
         end;
      end loop;
      return E_HAT;
   end NTT_Ref;
end RefMLKEM;

