with SumGen; use SumGen;

package body RecursNTT
    with SPARK_Mode => On
is


    function NTT_Recurs (E : Poly_Zq_Ref;
                         Psi : T_Ref;
                         Length : Positive) return NTT_Poly_Zq_Ref
    is
        A : NTT_Poly_Zq_Ref;
        B : NTT_Poly_Zq_Ref;
        Res : NTT_Poly_Zq_Ref;
        package Splitter_Poly is new Generic_Split_Sum (T_Ref, Index_Ref, Poly_Zq_Ref);
    begin
        if Length = 1 then
            Res (0) := E (0);
        else
            pragma Assert (Is_Pow_Of_Two (Length));
            pragma Assert (Length mod 2 = 0);
            pragma Assert ((Length / 2) = 1 or (Length / 2) mod 2 = 0);
            A := NTT_Recurs(Splitter_Poly.Extract_Even (E, Length), Psi * Psi, Length / 2);
            B := NTT_Recurs(Splitter_Poly.Extract_Odd (E, Length), Psi * Psi, Length / 2);
            for J in 0 .. (Length / 2 - 1) loop
                Res (Index_Ref (J)) := A (Index_Ref (J)) + Psi ** (2 * J + 1) * B (Index_Ref (J));
                Res (Index_Ref (J + Length / 2)) := A (Index_Ref (J)) - Psi ** (2 * J + 1) * B (Index_Ref (J));
            end loop;
        end if;
        return Res;
    end NTT_Recurs;

end RecursNTT;