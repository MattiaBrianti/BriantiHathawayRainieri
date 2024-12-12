open util/ordering[DateTime]

sig DateTime {}

sig Student {
	cv: lone CV, //Ogni studente può avere un solo CV (oppure non averlo se non compilato)
	preferences: set FieldOfInterest,
	currentInternships: lone Internship,
	matchedInternships: set Internship,
	notifications: set Notification,
	university: University
}

sig CV {
    owner: one Student,
    personalInfo: lone PersonalInfo,
    education: String,
    workExperience: String,
    technicalSkills: String,
    softSkills: String,
    projects: String,
    extracurricularActivities: String,
    certifications: String,
    languages: String,
    internshipPreferences: Bool,  //Only paid interships
    additionalInfo: String,
}

enum Bool { True, False }

sig PersonalInfo {
    name: String,
    contactInfo: String,
    personalAmbitions: String
}

sig Company {
	internshipOffers: set Internship,
	currentInternshipStudents: set Student,
	notifications: set Notification,
	complaints: set Complaint,
	feedback: set Feedback
} {
//Gli studenti per essere current devono svolgere un'internship offerta dall'azienda e avere lo stato "InProgress"
	all s: currentInternshipStudents|
		some i: internshipOffers |
			i in s.currentInternships and i.status = InProgress
}

sig Internship {
	company: Company, //Se non specifico è One
	attendingStudent: lone Student,
	description: String,
	requirements: String,
	status: InternshipState,
	matchedStudents: set Student,
}

sig University {
	students: set Student,            // Studenti iscritti all'università
	handledComplaints: set Complaint, // Reclami gestiti dall'università
	monitoredInternships: set Internship // Tirocini supervisionati
} {
	//Ogni internship di uno studente dell'università deve essere monitorata
	all s: Student | s in students implies (	
		all i:Internship | i in s.currentInternships => i in monitoredInternships
	)
}

//Feedback e Complaint sono due cose diverse perchè il sistema riconosce se l'internship è finita
sig Feedback {
	text: String,
	date: DateTime,
	author: one (Student + Company),
	receiver: one (Student + Company),
	referredInternship: Internship
}

sig Complaint {
	reason: String,
	referredInternship: Internship,
	author: one (Student + Company),
	resolved: Bool,
	date: DateTime,
	student: one Student,
	company: one Company,
	handledBy: one University
}

sig FieldOfInterest {}

sig Notification {
	content: String,
	createdOn: DateTime,
	receivedBy: one(Student + Company)
}

// States for internship
enum InternshipState { Waiting, Reviewing, Selection, InProgress, Terminated }

//Prima di contattare l'azienda lo studente deve avere il Cv completato
fact cvCompletionRequired {
    all s: Student | 
        all i: Internship | 
            (i in s.currentInternships and s.cv = none) => no i
}

// Uno studente può fare al massimo un internship alla volta
fact oneInternshipAtTime {
	all s: Student |
		lone i: s.currentInternships | i.status = InProgress
}

// Le notifiche di internship sono legate a internship che rientrano negli interessi dello studene
fact relevantNotification {
	all s: Student |
		all n: s.notifications |
			some i:Internship |
				i in s.matchedInternships and n.content in i.description
}

// se sto facendo un'internship o ho ricevuto/fatto richiesta, devo aver completato il CV
fact cvCompletionRequired {
	all s: Student |
		(some s.currentInternships or
		some i: s.matchedInternships | i.status != Waiting) =>
		some s.cv
}

// transizione dia matched a current
fact internshipStateTransition {
	all s: Student |
		all i: s.matchedInternships |
			i.status = InProgress implies (
				//L'internship deve essere rimossa da matchedInternships
				i not in s.matchedInternships and
				// Diventa la currentInternship se non ne esiste già un'altra
				(no s.currentInternships => s.currentInternships = i)
				)
}

// Quando un'internship passa allo stato Terminated viene eliminata dalla currentInternship dello studente
fact internshipTermination {
	all s: Student |
		all i: s.currentInternships |
			i.status = Terminated implies no s.currentInternships
}

//Se un'azienda lascia un feedback deve essere ricevuto dallo studente e viceversa
fact reciprocalFeedback {
	all f: Feedback |
		some f2: Feedback |
			f2.receiver = f.author and f2.author = f.receiver
}

//VINCOLI INTERNSHIP

// Lo stato dell'internship è in progress solo se c'è uno studente
fact statusInProgress {
	all i: Internship |
		i.status = InProgress implies some i.attendingStudent
}

// Gli stage non possono essere in Selection se non ci sono studenti candidati
fact statusSelection {
	all i: Internship |
		i.status = Selection implies some i.matchedStudents
}

//Ogni tirocinio attivo deve essere monitorato da un'università
fact monitoredInternships {
	all i: Internship |
	i.status = InProgress implies some u:University | i in u.monitoredInternships
}

//VINCOLI COMPLAINT

// I reclami devono essere legati a stage supervisionati
fact validComplaints {
	all c: Complaint |
		c.referredInternship in c.handledBy.monitoredInternships
}

//VINCOLI FEEDBACK

// I feedback possono essere inviati solo per stage terminati:
fact feedbackTerminated {
	all f: Feedback |
		f.referredInternship.status = Terminated
}

//VINCOLI GENERALI

//Consistenza delle notifiche
fact validNotifications {
	all n: Notification |
		some n.content and some n.receivedBy
}

