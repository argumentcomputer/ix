  obtain ⟨h1, h2, h3⟩ := sound h D hD i hi
  refine ⟨fun k w hw => (h1 k w hw).imp_right (Front.goesWrong_live h hsa), fun hn => h2 ?_, h3⟩
  exact fun hg => hn (Front.goesWrong_live h hsa hg)
