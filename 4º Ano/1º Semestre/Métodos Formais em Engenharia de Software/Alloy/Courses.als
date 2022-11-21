open util/ordering[Grade]

sig Person {
	teaches : set Course,
	enrolled : set Course,
	projects : set Project
}

sig Professor,Student in Person {}

sig Course {
	projects : set Project,
	grades : Person -> Grade
}

sig Project {}

sig Grade {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

pred inv1 {
	// Only students can be enrolled in courses
  	enrolled.Course in Student
}


pred inv2 {
	// Only professors can teach courses
  	teaches.Course in Professor
	
}


pred inv3 {
	// Courses must have teachers
  	all c: Course | some teaches.c
}


pred inv4 {
	// Projects are proposed by one course
	all p: Project | one Course :> projects.p
}


pred inv5 {
	// Only students work on projects and 
	// projects must have someone working on them
  	Person :> projects.Project in Student
  	all p: Project | some Person :> projects.p
}


pred inv6 {
	// Students only work on projects of courses they are enrolled in
  	all s: Student | s.projects in s.enrolled.projects
}


pred inv7 {
	// Students work on at most one project per course
  	all s: Student | all c: s.enrolled | lone c.projects & s.projects

}


pred inv8 {
	// A professor cannot teach herself
  	all t: Professor | all c: t.teaches | t.enrolled in Course-c 

}


pred inv9 {
	// A professor cannot teach colleagues
  	//all p: Professor |all cour: p.teaches | all col: teaches.cour |  cour not in col.enrolled
    all p1, p2 : Professor | all c: Course | c in p1.teaches and c in p2.teaches implies no p1.teaches & p2.enrolled
}


pred inv10 {
	// Only students have grades
  	all p : Person | p in Course.grades.Grade implies p in Student
}


pred inv11 {
	// Students only have grades in courses they are enrolled
    all s: Student | all c: Course | s in c.grades.Grade implies c in s.enrolled
}


pred inv12 {
	// Students have at most one grade per course
    all s: Student | all c: Course | lone ~(c.grades).s
}


pred inv13 {
	// A student with the highest mark in a course must have worked on a project on that course
    all s: Student | all c: Course | s in c.grades.last implies some s.projects & c.projects
}

pred inv14 {
	// A student cannot work with the same student in different projects
    all s1, s2 : Student | s1 != s2 implies lone s1.projects & s2.projects
}


pred inv15 {
	// Students working on the same project in a course cannot have marks differing by more than one unit
    all p : Project | all s1,s2 : Student | all c : Course | (s1!=s2 and p in s1.projects and p in s2.projects and p in c.projects) implies 
    (all g1,g2 : Grade | g1 in s1.(c.grades) and g2 in s2.(c.grades) implies 
    (g1=prev[g2] or g2=prev[g1] or g1=g2))
}