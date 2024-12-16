open util/ordering[DateTime]

sig DateTime {}

sig Student {
	cv: lone CV, //Ogni studente può avere un solo CV (oppure non averlo se non compilato)
	preferences: some FieldOfInterest,
	currentInternships: lone Internship,
	matchedInternships: set Internship,
	notifications: set Notification,
	university: University,
    complaintsDone: set Complaint,
    complaintsReceived: set Complaint,
    feedbackDone: set Feedback,
    feedbackReceived: set Feedback
}{
	all c: CV | c in cv <=> c.owner = this
	all i: Internship | i in currentInternships <=> i.attendingStudent = this
	all i: Internship | i in matchedInternships <=> i.matchedStudents = this
    
    //Per ogni studente che sta facendo un'internship implica che abbia il CV
	all i: Internship | i in currentInternships implies (some cv and cv.owner=this)
    
    //Per ogni studente che ha fatto richiesta di un'internship (quindi stato diverso dal Waiting) deve esserci il proprio CV
    all i: Internship | i in matchedInternships and i.status != Waiting implies (some cv and cv.owner=this)
    
    //Quando lo stato di una matchedInternships diventa InProgress
    //l'Internship viene rimossa da matchedInternships e diventa currentInternships
    all i: Internship | i in matchedInternships and i.status = InProgress implies (
        i not in matchedInternships and
        (no currentInternships => currentInternships = i)
    )

    //Quando un'Internship passa allo stato terminated viene eliminata dalla currentInternships dello studente
    all i: Internship | i in currentInternships and i.status = Terminated implies no currentInternships
    
	all n: Notification | n in notifications <=> n.receivedBy = this
    all f: FieldOfInterest | f in preferences <=> f.user = this
    all c: Complaint | c in complaintsDone <=> c.author = this
    all c: Complaint | c in complaintsReceived <=> c.receiver = this
    all f: Feedback | f in feedbackDone <=> f.author = this
    all f: Feedback | f in feedbackReceived <=> f.receiver = this
    
    // Uno studente può inviare feedback solo alla company della sua currentInternships in stato InProgress
    all f: Feedback | f in feedbackDone implies (
        f.receiver in Company and
        f.referredInternship = currentInternships and
        currentInternships.status = InProgress and
        currentInternships.company = f.receiver
    )
 }

sig CV {
    owner: one Student,
}

sig Company {
	internshipOffers: set Internship,
	notifications: set Notification,
	complaintsReceived: set Complaint,
	complaintsDone: set Complaint,
	feedbackDone: set Feedback,
    feedbackReceived: set Feedback
} {
    all i: Internship | i in internshipOffers <=> i.company = this
    all n: Notification | n in notifications <=> n.receivedBy = this
    all c: Complaint | c in complaintsDone <=> c.author = this
    all c: Complaint | c in complaintsReceived <=> c.receiver = this
    all f: Feedback | f in feedbackDone <=> f.author = this
    all f: Feedback | f in feedbackReceived <=> f.receiver = this
    
    // Una company può inviare feedback solo allo studente della sua currentInternships in stato InProgress
    all f: Feedback | f in feedbackDone implies (
        f.receiver in Student and
        f.referredInternship in internshipOffers and
        f.referredInternship.status = InProgress and
        f.referredInternship.attendingStudent = f.receiver
    )
}

sig Internship {
	company: Company,
	attendingStudent: lone Student,
	status: InternshipState,
	matchedStudents: set Student,
    monitor: lone University
} {
  all s: Student | s in matchedStudents <=> s.matchedInternships = this
  // Lo stato di un'internship è InProgress solo se è una currentInternship di uno studente
  status = InProgress implies some s: Student | this = s.currentInternships
  // Lo stato di un'internship non può essere Reviewing o Selection se non ci sono studenti che l'hanno in matchedInternships
  (status = Reviewing or status = Selection) implies some s: Student | this in s.matchedInternships
  // L'University deve essere presente solo se lo stato è InProgress
  status = InProgress implies some monitor
}

sig University {
	students: set Student,            // Studenti iscritti all'università
	complaintsReceived: set Complaint, // Reclami ricevuti dall'università
    complaintsDone: set Complaint, // Reclami inviati dall'università
	monitoredInternships: set Internship // Tirocini supervisionati
} {
	all s: Student | s in students <=> s.university = this
    all c: Complaint | c in complaintsDone <=> c.author = this
    all c: Complaint | c in complaintsReceived <=> c.receiver = this
    all i: Internship | i in monitoredInternships <=> i.monitor = this
}

sig Feedback {
	date: DateTime,
	author: one (Student + Company),
	receiver: one (Student + Company),
	referredInternship: Internship
} {
    // Collegamento del feedback all'autore
    all s: Student | author = s implies this in s.feedbackDone
    all c: Company | author = c implies this in c.feedbackDone
    
    // Collegamento del feedback al ricevitore
    all s: Student | receiver = s implies this in s.feedbackReceived
    all c: Company | receiver = c implies this in c.feedbackReceived
}

sig Complaint {
	referredInternship: Internship,
	author: one (Student + Company + University),
	subject: one (Student + Company),
	date: DateTime,
	receiver: one (Student + Company + University)
} {

    // Collegamento del feedback all'autore
    all s: Student | author = s implies this in s.complaintsDone
    all c: Company | author = c implies this in c.complaintsDone
    
    // Collegamento del feedback al ricevitore
    all s: Student | receiver = s implies this in s.complaintsReceived
    all c: Company | receiver = c implies this in c.complaintsReceived

    // Vincolo: Se l'autore è uno studente o una compagnia, il destinatario deve essere un'università
    (author in Student or author in Company) implies receiver in University

    (author in Student) implies subject in Company

    // Vincolo: Se l'autore è un'università, il destinatario deve essere uno studente o una compagnia
    author in University implies (receiver in Student or receiver in Company)

    (author in Company) implies subject in Student
}

abstract sig Topic {}
one sig DataAnalysis, MachineLearning, WebDevelopment, CyberSecurity, CloudComputing extends Topic {}

sig FieldOfInterest {
	topic: one Topic,
    	user: set Student 
}

//Non possono esistere 2 field of interest uguali
fact UniqueTopicsForFieldOfInterest {
    all disj f1, f2: FieldOfInterest | f1.topic != f2.topic
}

sig Notification {
	createdOn: DateTime,
	receivedBy: one(Student + Company)
}

// States for internship
enum InternshipState { Waiting, Reviewing, Selection, InProgress, Terminated }

// Per ogni complaint se l'autore è uno studente allora deve essere lo stesso che sta facendo l'internship
fact StudentComplaintRefersToCurrentInternship {
    all c: Complaint | c.author in Student implies c.author.currentInternships = c.referredInternship
}

// Per ogni complaint se l'autore è una Company allora deve essere la stessa company che ha creato l'internship
fact CompanyComplaintRefersToItsInternship {
    all c: Complaint | c.author in Company implies c.author = c.referredInternship.company
}

//Per ogni Complaints se il soggetto è uno studente deve essere lo stesso che sta facendo l'internship
fact CompanyComplaintRefersToItsInternship {
    all c: Complaint | c.author in Company implies c.subject = c.referredInternship.attendingStudent
}

run {
	#Student = 1
	#CV = 1
	#Company = 2
	#Internship = 2
		some i: Internship | i.status = InProgress
	#University = 1
	#FieldOfInterest = 2
	#Notification = 3
	#Feedback = 0
	#Complaint = 1
} for 10


//Devo aggiungere la condizione che un'internship ha dei FieldOfInterest e devono essere gli stessi dello student per essere matchati e per far arrivare la notifica (?)