open util/ordering[DateTime]

sig DateTime{}

sig Student {
	initialForm: set InitialForm,
	cv: set CV,
	application: set Application,
	preferences: Preferences,
	currentInternship: lone Internship,
	matchedInternships: set Internship,
	notifications: set Notification,
	university: one University,
	reportAuthor: set Report,
	questionnaireAuthor: set Questionnaire,
	messageAuthor: set ChatMessage,
	messageReceiver: set ChatMessage,
	logbook: set Logbook
} {
	all i: InitialForm | i in initialForm <=> i.author = this
	all c: CV | c in cv <=> c.owner = this
	all a: Application | a in application <=> a.student = this
	all i: Internship | i in currentInternship <=> i.currentStudent = this
	all i: Internship | i in matchedInternships <=> i.matchedStudents = this
	all r: Report | r in reportAuthor <=> r.author = this
	all q: Questionnaire | q in questionnaireAuthor <=> q.author = this
	all c: ChatMessage | c in messageAuthor <=> c.author = this
	all c: ChatMessage | c in messageReceiver <=> c.receiver = this
	all l: Logbook | l in logbook <=> l.author = this

	//For each student doing an internship implies that they have the CV
	all i: Internship | (i in currentInternship or (i in matchedInternships 
	and i.state != Waiting)) 
		implies (some cv and cv.owner = this)

	//When an internship becomes InProgress, it is removed from matchedInternships
	//and becomes a CurrentInternship
	all i: Internship | i in matchedInternships and i.state = InProgress implies (
	i not in matchedInternships and (no currentInternship => currentInternship = i))
	
	//When an internship changes to Terminated status,
	//it is deleted from the student's currentInternship
	all i: Internship | i in currentInternship and i.state = Terminated 
		implies no currentInternship

	//For every CV of the student, the student must be linked 
	//to the corresponding Application
	all c: CV | c in cv implies one a: Application | a.cv = c and a.student = this
}

sig Notification {}
sig Preferences{}

sig InitialForm {
	author: one Student,
	cvGenerated: set CV
} {
	all s: Student | s in author <=> s.initialForm = this
	all c: CV | c in cvGenerated <=> c.initialForm = this
	all c: CV | c in cvGenerated implies c.owner.initialForm = this
}

sig CV {
	owner: one Student,
	application: one Application,
	initialForm: one InitialForm
}{
	all s: Student | s in owner <=> s.cv = this
	all a: Application | a in application <=> a.cv = this
	all i: InitialForm | i in initialForm <=> i.cvGenerated = this
}

sig Application {
	student: one Student,
	cv: one CV,
	internship: one Internship
} {
	all s: Student | s in student <=> s.application = this
	all c: CV | c in cv <=> c.application = this
	all i: internship | i in internship <=> i.applications = this
}

sig Company {
	internshipsCreated: set Internship,
	messageAuthor: set ChatMessage,
	messageReceiver: set ChatMessage,
	questionnaireAnalyzer: set Questionnaire,
	reportAuthor: set Report,
	notifications: Notification,
} {
	all i: Internship | i in internshipsCreated <=> i.company = this
	all c: ChatMessage | c in messageAuthor <=> c.author = this
	all c: ChatMessage | c in messageReceiver <=> c.receiver = this
	all q: Questionnaire | q in questionnaireAnalyzer <=> q.receiver = this
	all r: Report | r in reportAuthor <=> r.author = this
}

sig Internship {
	applications: set Application,
	state: InternshipState,
	currentStudent: lone Student,
	matchedStudents: set Student,
	company: Company,
	description: String,
	monitor: lone University 
} {
	all a: Application | a in applications <=> a.internship = this
	all s: Student | s in currentStudent <=> s.currentInternship = this
	all s: Student | s in matchedStudents <=> s.matchedInternships = this
	all c: Company | c in company <=> c.internshipsCreated = this
	all u: University | u in monitor <=> u.monitoredInternship = this
	description = "Description"

	//The status of an internship is InProgress only 
	//if it is a currentInternship of a student
	state = InProgress 
		implies some s: Student | this = s.currentInternship
	//The status of an internship cannot be Reviewing or Selection
	//if there are no students who have it in matchedInternships
	(state = Reviewing or state = Selection) 
		implies some s: Student | this in s.matchedInternships
	//The University must only be present if the status is in Progress
	state = InProgress implies some monitor
}

sig University {
	students: set Student,
	reportsReceived: set Report,
	monitoredInternship: set Internship,
	messageAuthor: set ChatMessage,
	messageReceiver: set ChatMessage,
	logbook: set Logbook
} {
	all s: Student | s in students <=> s.university = this
	all r: Report | r in reportsReceived <=> r.receiver = this
	all i: Internship | i in monitoredInternship <=> i.monitor = this
	all c: ChatMessage | c in messageAuthor <=> c.author = this
	all c: ChatMessage | c in messageReceiver <=> c.receiver = this
	all l: Logbook | l in logbook <=> l.reader = this
}

sig Report {
	author: one (Student + Company),
	receiver: one University,
} {
	all s: Student | s in author <=> s.reportAuthor = this
	all c: Company | c in author <=> c.reportAuthor = this
	all u: University | u in receiver <=> u.reportsReceived = this
}

sig Questionnaire {
	author: one Student,
	receiver: one Company
} {
	all s: Student | s in author <=> s.questionnaireAuthor = this
	all c: Company | c in receiver <=> c.questionnaireAnalyzer = this
}

sig ChatMessage {
	author: one (Student + Company + University),
	receiver: one (Student + Company + University)
} {
	all s: Student | s in author <=> s.messageAuthor = this
	all c: Company | c in author <=> c.messageAuthor = this
	all u: University | u in author <=> u.messageAuthor = this
	all s: Student | s in receiver <=> s.messageReceiver = this
	all c: Company | c in receiver <=> c.messageReceiver = this
	all u: University | u in receiver <=> u.messageReceiver = this

	//A user may not write messages to a user of the same type
	all s: Student | s in author implies s.messageReceiver in 
		(Company.messageReceiver + University.messageReceiver)
	all c: Company | c in author implies c.messageReceiver in
		(Student.messageReceiver + University.messageReceiver)
	all u: University | u in author implies u.messageReceiver in
		(Student.messageReceiver + Company.messageReceiver)
}

sig Logbook {
	author: one Student,
	reader: one University
} {
	all s: Student | s in author <=> s.logbook = this
	all u: University | u in reader <=> u.logbook = this
}

// States for internship
enum InternshipState { Waiting, Reviewing, Selection, InProgress, Terminated }
	