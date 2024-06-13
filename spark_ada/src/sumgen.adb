
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body SumGen 
    with SPARK_Mode => On
is
    package body Sum_On_Array is 

        function Sum (A : InputType;
                              Max_Index : IndexRange) return ElementType
        is (if Max_Index = 0 then A (0) else Sum (A, Max_Index - 1) + A (Max_Index));


        function Replace_By_Zeros (X : InputType;
                                   A : IndexRange) return InputType
        is
            Res : InputType;
        begin
            for J in IndexRange loop
                if J > A then
                    Res (J) := 0;
                else
                    Res (J) := X(J);
                end if;
            end loop;
            return Res;
        end Replace_By_Zeros;

        function "+" (F : InputType;
                      G : InputType) return InputType
        is
            Res : InputType with Relaxed_Initialization;
        begin
            for I in IndexRange loop
                Res (I) := F (I) + G (I);
                pragma Loop_Invariant (for all J in 0 .. I => 
                                        Res(J)'Initialized and then 
                                        (Res (J) = F (J) + G (J)));
            end loop;
            return Res;
        end "+";

        function Lemma_Sum_Disjoint (F : InputType;
                                             G : InputType;
                                             Max_Index : IndexRange) return Boolean
        is
            H : InputType := F + G;
            Tiny_Sum_F : ElementType;
            Tiny_Sum_G : ElementType;
            Tiny_Sum_H : ElementType;
            Induction_Hypothesis : Boolean;
            Sum_F : ElementType := Sum (F, Max_Index);
            Sum_G : ElementType := Sum (G, Max_Index);
            Sum_H : ElementType := Sum (H, Max_Index);
        begin
            if (Max_Index = 0) then
                pragma Assert (Sum_F + Sum_G = Sum_H);
            elsif (Max_Index > 0) then
                Tiny_Sum_F := Sum (F, Max_Index - 1); 
                pragma Assert (Sum_F = Tiny_Sum_F + F (Max_Index));
                Tiny_Sum_G := Sum (G, Max_Index - 1); 
                pragma Assert (Sum_G = Tiny_Sum_G + G (Max_Index));
                Tiny_Sum_H := Sum (H, Max_Index - 1); 
                pragma Assert (Sum_H = Tiny_Sum_H + H (Max_Index));

                Induction_Hypothesis := Lemma_Sum_Disjoint (F, G, Max_Index - 1);

                pragma Assert (By (Tiny_Sum_F + Tiny_Sum_G = Tiny_Sum_H, Induction_Hypothesis));

                pragma Assert (F (Max_Index) + G (Max_Index) = H (Max_Index));
                pragma Assert ((Tiny_Sum_F + Tiny_Sum_G) + (F (Max_Index) + G (Max_Index)) = Tiny_Sum_H + H (Max_Index));
                pragma Assert (By (
                    (Tiny_Sum_F + Tiny_Sum_G) + (F (Max_Index) + G (Max_Index)) = (((Tiny_Sum_F + Tiny_Sum_G) + F (Max_Index)) + G (Max_Index)),
                    Lemma_Add_Associative (Tiny_Sum_F + Tiny_Sum_G, F (Max_Index), G (Max_Index))
                ));
                pragma Assert (By (
                    ((Tiny_Sum_F + Tiny_Sum_G) + F (Max_Index)) + G (Max_Index) = (Tiny_Sum_F + (Tiny_Sum_G + F (Max_Index))) + G (Max_Index),
                    Lemma_Add_Associative (Tiny_Sum_F, Tiny_Sum_G, F (Max_Index))
                ));
                pragma Assert (By (
                    (Tiny_Sum_F + (Tiny_Sum_G + F (Max_Index))) + G (Max_Index) = Tiny_Sum_F + (F (Max_Index)+ Tiny_Sum_G) + G (Max_Index),
                    Lemma_Add_Commutative (F (Max_Index), Tiny_Sum_G)
                ));
                pragma Assert (By (
                    Tiny_Sum_F + (F (Max_Index)+ Tiny_Sum_G) + G (Max_Index) = ((Tiny_Sum_F + F (Max_Index)) + Tiny_Sum_G) + G (Max_Index),
                    Lemma_Add_Associative (Tiny_Sum_F, F(Max_Index), Tiny_Sum_G)
                ));
                pragma Assert (By (
                    ((Tiny_Sum_F + F (Max_Index)) + Tiny_Sum_G) + G (Max_Index) = (Tiny_Sum_F + F (Max_Index)) + (Tiny_Sum_G + G (Max_Index)),
                    Lemma_Add_Associative (Tiny_Sum_F + F (Max_Index), Tiny_Sum_G, G (Max_Index))
                ));
                pragma Assert ((Tiny_Sum_F + F (Max_Index))+ (Tiny_Sum_G + G (Max_Index)) = Tiny_Sum_H + H (Max_Index));
                pragma Assert (Sum_F + Sum_G = Sum_H);
            end if;
            return True;
        end Lemma_Sum_Disjoint;

        function Lemma_Add_Associative (A : ElementType;
                                        B : ElementType;
                                        C : ElementType) return Boolean
        is (True);

        function Lemma_Add_Commutative (A : ElementType;
                                        B : ElementType) return Boolean
        is (True);

    end Sum_On_Array;

    function Is_Pow_Of_Two (A : Positive) return Boolean
    is
        (A = 1 or (A mod 2 = 0 and Is_Pow_Of_Two (A / 2)));

    package body Generic_Split_Sum 
        with SPARK_Mode => On
    is 
        function Extract_Even (F : ArrayType; 
                               Length : Integer) return ArrayType
        is 
            Res : ArrayType (0 .. Length / 2 - 1) with Relaxed_Initialization;
        begin
            for I in 0 .. (Length / 2 - 1) loop
                Res (IndexRange (I)) := F (IndexRange (2 * I));
                pragma Loop_Invariant (for all J in 0 .. I => 
                    Res (IndexRange (J))'Initialized and
                    Res (IndexRange (J)) = F (IndexRange (2 * J))
                );
            end loop;
            return Res;
        end Extract_Even;

        function Extract_Odd (F : ArrayType;
                              Length : Integer) return ArrayType
        is 
            Res : ArrayType with Relaxed_Initialization;
        begin
            for I in 0 .. (Length / 2 - 1) loop
                Res (IndexRange (I)) := F (IndexRange (2 * I + 1));
                pragma Loop_Invariant (for all J in 0 .. I => 
                    Res (IndexRange (J))'Initialized and
                    Res (IndexRange (J)) = F (IndexRange (2 * J + 1))
                );
            end loop;
            return Res;
        end Extract_Odd;

        function Lemma_Split_Odd_Even (A :  ArrayType;
                                       Length : Integer) return Boolean
        is
            (True);
    end Generic_Split_Sum;

    package body Generic_Apply_To_Array is
        function Apply_To_Array (X : InputTypeA) return InputTypeB
        is
            Res : InputTypeB;
        begin
            for I in IndexRange loop
                Res (I) := Func (X (I));
            end loop;
            return Res;
        end Apply_To_Array;
    end Generic_Apply_To_Array;

end SumGen;