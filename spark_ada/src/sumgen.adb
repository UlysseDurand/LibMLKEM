
package body SumGen 
    with SPARK_Mode => On
is

    package body Generic_Sum 
        with SPARK_Mode => On
    is
        function Sum (P1 : Type1;
                      P2 : Type2;
                      A : IndexRange;
                      B : IndexRange) return returnType
        is
            (if B < A then Zero elsif B = A then Func (P1, P2, A) else Sum (P1, P2, A, B -1) + Func (P1, P2, B));
        --  is
        --      Res : ReturnType := Zero;
        --      begin
        --      for J in A .. B loop
        --          Res := Res + Func (P1, P2, J);
        --      end loop;
        --      return Res;
        --  end Sum;

        function Lemma_Sum_Splitable (P1 : Type1;
                                      P2 : Type2;
                                      A : IndexRange; 
                                      B : IndexRange; 
                                      C : IndexRange) return Boolean
        is 
        begin
            pragma Assert (Sum(P1, P2, A, B) = (if B < A then Zero elsif B = A then Func (P1, P2, A) else Sum (P1, P2, A, B -1) + Func (P1, P2, B)));
            pragma Assert (if A = C - 1 then Sum (P1, P2, A, C - 1) = Func (P1, P2, A));
            pragma Assert (Sum (P1, P2, A, C - 1) + Sum (P1, P2, C, B) = Sum (P1, P2, A, C));
            return True;
        end Lemma_Sum_Splitable;
    end Generic_Sum;

end SumGen;