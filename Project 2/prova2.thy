theory prova2
imports Main

begin
theorem p2:
  assumes pq: "P\<or>Q"
  shows "\<not>(\<not>P \<and> \<not>Q)"

proof -
  have npnqFalse: "(\<not>P \<and> \<not>Q) \<Longrightarrow> False"
  proof -
    assume npnq: "(\<not>P \<and> \<not>Q)"
    from npnq have np: "\<not>P" by (rule conjE)
    from npnq have nq: "\<not>Q" by (rule conjE)
    have pfalse: "P \<Longrightarrow> False"
    
    proof -
      assume p: "P"
      from np and p show "False" by (rule notE)
    qed

    have qfalse: "Q \<Longrightarrow> False"
    proof -
      assume q: "Q"
      from nq and q show "False" by (rule notE)
    qed
    from pq and pfalse and qfalse show contra:"False" by (rule disjE)
  qed
  from npnqFalse show "\<not>(\<not>P\<and>\<not>Q)" by (rule notI)
qed
end
