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

sig PersonalData extends NonCommentable {
	data: MyString
}

sig Message extends NonCommentable {
	text: MyString,
	//sender: ActorID
}




/*
abstract sig Commentable extends Content {
	comments: set String
}

sig Photo extends Commentable {
	photoLink: set String
}
*/

/*
abstract sig NonCommentable extends Content {}

// a Photo content is modeled as a link to a picture
sig Photo extends Commentable {
	photoLink: String
}

// a post contains text and optionally link(s) to Photos
sig Post extends Commentable {
	text: String,
	photoLink: set String
}

// each personal data is modeled as individual content
sig PersonalData extends NonCommentable {
	data: String
}

// a message contains text
sig Message extends NonCommentable {
	text: String
	//sender: ActorID
	//receiver: ActorID
}
*/

pred show {}

run show
