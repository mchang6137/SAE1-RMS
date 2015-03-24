// string class
sig MyString {}

// ************************************** PRIVACY SETTINGS *********************************** //
abstract sig Privacy {}
abstract sig PersonalLevel, GroupLevel extends Privacy {}
// personal profile settings
abstract sig Circles extends PersonalLevel {}
one sig Private, Friends, FriendsOfFriends, TransitiveFriends, PPublic extends Circles {} // posts
one sig OneToOne extends PersonalLevel {} // messages
// group profile settings
one sig GPublic, Group extends GroupLevel {}


// ************************************** CONTENT ******************************************* //
// every content has a privacy setting and an owner
abstract sig Content {
	//owner: ActorID
	privacySetting: Privacy
}

abstract sig NonCommentable extends Content {}

abstract sig Commentable extends Content {
	comments: set MyString,
	photoLink: lone MyString
} {
	// photo link and comments are different strings; check for none is required to allow for an empty photoLink
	photoLink != none => photoLink not in comments
	// visibility of all commentable content is given by circles
	// TO DO: move and specify this once userIDs and groupIDs are available
	privacySetting in (Circles + GroupLevel)
}

// groups also have PersonalData (e.g. group name)
sig PersonalData extends NonCommentable {
	data: MyString
} {
	// visibility is given by circles
	// TO DO: move and specify this once userID and groupIDs are available
	privacySetting in (Circles + GroupLevel)
}

sig Message extends NonCommentable {
	text: MyString,
	photoLink: lone MyString
	//sender: ActorID
} {
	// photo link and text are different strings; check for none is required to allow for an empty photoLink
	photoLink != none => photoLink != text
	// message is either visible to the reciever or public
	privacySetting in (OneToOne + PPublic)
}

sig Photo extends Commentable {
} {
	// there has to be a photo link
	one photoLink
}

sig Post extends Commentable {
	text: MyString,
} {
	// text and photo link are different strings; check for none is required to allow for an empty photoLink
	photoLink != none => text !=photoLink
	// text and comments are different strings
	text not in comments
}


// no string is shared
fact {
	// among objects of the same signature
	all disj c1, c2: Commentable | ((c1.comments+c1.photoLink) & (c2.comments+c2.photoLink)) = none
	all disj p1, p2: PersonalData | p1.data != p2.data
	all disj m1, m2: Message | ((m1.text+m1.photoLink) & (m2.text+m2.photoLink)) = none
	all disj p1, p2: Post | p1.text != p2.text && p1.text not in (p2.comments+p2.photoLink) && p2.text not in (p1.comments+p1.photoLink)
	// among objects of different signatures
	all d: PersonalData, m: Message | (d.data & (m.text+m.photoLink)) = none
	all d: PersonalData, p: Photo | (d.data & (p.comments+p.photoLink)) = none
	all d: PersonalData, p: Post | (d.data & (p.comments+p.photoLink+p.text)) = none
	all m: Message, p: Photo | ((m.text+m.photoLink) & (p.comments+p.photoLink)) = none
	all m: Message, p: Post | ((m.text+m.photoLink) & (p.comments+p.photoLink+p.text)) = none
	all ph: Photo, po: Post | po.text not in (ph.comments+ph.photoLink) // rest is ensured above
	all d: PersonalData, m: Message, p: Photo | (d.data & (m.text+m.photoLink) & (p.comments+p.photoLink)) = none
	all d: PersonalData, m: Message, p: Post | (d.data & (m.text+m.photoLink) & (p.comments+p.photoLink+p.text)) = none
	all d: PersonalData, ph: Photo, po: Post | (d.data & (ph.comments+ph.photoLink) & (po.comments+po.photoLink+po.text)) = none
	all m: Message, ph: Photo, po: Post | ((m.text+m.photoLink) & (ph.comments+ph.photoLink) & (po.comments+po.photoLink+po.text)) = none
	all d: PersonalData, m: Message, ph: Photo, po: Post | (d.data & (m.text+m.photoLink) & (ph.comments+ph.photoLink) & (po.comments+po.photoLink+po.text)) = none
}

// all strings are connected to content
fact {
	#MyString = #(Commentable.comments + Commentable.photoLink + PersonalData.data + Message.text + Message.photoLink + Post.text)
}


pred show {}

run show for 10 Privacy, 8 MyString, exactly 3 Commentable, exactly 3 NonCommentable
