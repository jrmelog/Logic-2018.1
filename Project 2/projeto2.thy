theory projeto2
imports Main

begin
theorem prova1:
  assumes p_qr: "P \<or> (Q\<and>R)"
  shows "(P\<or>Q) \<and> (P\<or>R)"

  proof -
    have p_pq_and_pr: "P \<Longrightarrow>(P\<or>Q) \<and> (P\<or>R)"
    proof -
      assume p: "P"
      from p have pq: "(P\<or>Q)" by (rule disjI1)
      from p have pr: "(P\<or>R)" by (rule disjI1)
      from pq and pr show "(P\<or>Q) \<and> (P\<or>R)" by (rule conjI)
    qed
    
    have qr_pq_and_pr: "(Q\<and>R) \<Longrightarrow>(P\<or>Q) \<and> (P\<or>R)"
    proof -
      assume qr:"(Q\<and>R)"
      from qr have q: "Q" by (rule conjE)
      from qr have r: "R" by (rule conjE)
      from q have pq: "(P\<or>Q)" by (rule disjI2)
      from r have pr: "(P\<or>R)" by (rule disjI2)
      from pq and pr show "(P\<or>Q) \<and> (P\<or>R)" by (rule conjI)
    qed
  from p_qr and p_pq_and_pr and qr_pq_and_pr show "(P\<or>Q)\<and>(P\<or>R)" by (rule disjE)
qed

theorem prova2:
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
