/*************************************************/
/** SAE 2015, Project Part 1                                                          **/
/**                                                                                                     **/
/** TEAM: RMS                                                                                  **/
/** ------------                                                                                  **/
/** Michael Chang (14-910-533)                                                   **/
/** Rik Melis          (14-908-875)                                                   **/
/** Simon Tödtli     (09-925-934)                                                  **/
/**                                                                                                     **/
/** ETHZ, March 15                                                                          **/
/*************************************************/

/** TASK B **/
// ===================================================//
//                                  SOCIAL NETWORK                                                     //
//===================================================//
// social network is a set of interacting actors
// there is only one single social network
one sig SocialNetwork {
	actors: set ActorID
}


//===================================================//
//                                            ACTORS                                                          //
//===================================================//
// every actor of the social network is identified by a unique id
// users and groups have different capabilities, therefore treat them separately
abstract sig ActorID {}
sig UserID, GroupID extends ActorID {}


// every actor (user / group) has a list of allowed and blocked followers
abstract sig Actor {
	allowedFollowers: set UserID,
	blockedFollowers: set UserID,
} {
	// a follower is either allowed or blocked
	no f: UserID | f in allowedFollowers && f in blockedFollowers
}

sig PersonalProfile extends Actor {
	id: UserID,
	friends: set UserID
} {
	// user is not it's own friend
	id not in friends
	// user doesn't follow or block itself
	id not in allowedFollowers && id not in blockedFollowers
}

sig GroupProfile extends Actor {
	id: GroupID,
	// every group has at least one group member and administrator
	groupMembers: some UserID,
	administrators: some UserID
} {
	// administrator must be group member
	no m: UserID | m in administrators && m not in groupMembers
}

// actor constraints
// ---------------------
// no id exists outside the social network
fact {
	no uid: UserID, s: SocialNetwork | uid not in s.actors
	no gid: GroupID, s: SocialNetwork | gid not in s.actors
}

// IDs are unique
fact {
	all disj p1, p2: PersonalProfile | p1.id !=  p2.id
	all disj g1, g2: GroupProfile | g1.id != g2.id
}

// every actor in the social network is either a user or a group
fact {
	#(SocialNetwork.actors) = # (PersonalProfile + GroupProfile)
}

// friendships are mutual
fact {
	all disj p1, p2: PersonalProfile | p1.id in p2.friends <=> p2.id in p1.friends
}


//===================================================//
//                                 PRIVACY SETTINGS                                                    //
//===================================================//
abstract sig Privacy {}
abstract sig PersonalLevel, GroupLevel extends Privacy {}

// personal profile settings
abstract sig Circles extends PersonalLevel {}
one sig Private, Friends, FriendsOfFriends, TransitiveFriends, PPublic extends Circles {} // posts
one sig OneToOne extends PersonalLevel {} // messages

// group profile settings
one sig GPublic, Group extends GroupLevel {}


//==================================================//
//                                         CONTENT                                                         //
//==================================================//
// string class (alloy's built in Strings suck)
sig MyString {}

abstract sig Content {
	owner: ActorID,
	privacySetting: Privacy
}

// superclass for personal data and messages (non commentable content)
abstract sig NonCommentable extends Content {}

// superclass for post, photo (commentable content)
abstract sig Commentable extends Content {
	comments: set MyString,
	photoLink: lone MyString
} {
	// photo link and comments are different strings
	// check for none is required to allow for an empty set photoLink
	photoLink != none => photoLink not in comments
	// (i) group content                                                   (ii) user content privacy
	owner in GroupID => privacySetting in GroupLevel else privacySetting in Circles
}

sig PersonalData extends NonCommentable {
	data: MyString
} {
	// (i) group content                                                    (ii) user content privacy
	owner in GroupID => privacySetting in GroupLevel else privacySetting in Circles
}

sig Message extends NonCommentable {
	text: MyString,
	photoLink: lone MyString,
	receiver: UserID // the sender of the message is given by owner
} {
	// photo link and text are different strings
	// check for none is required to allow for an empty photoLink
	photoLink != none => photoLink != text
	// groups can't send messages
	owner in UserID
	// sender and receiver must be two different users
	receiver != owner
	// message is either visible to the reciever or public
	privacySetting in (OneToOne + PPublic)
}

sig Photo extends Commentable {
} {
	// we model a photo post to only contain the link to the photo (which is stored elsewhere)
	// therefore, photoLink has to be non-empty
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


// constraints
// --------------
// no string is shared (this is super ugly, but works)
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

// details not modeled:
// - admins can remove group members (this is a static model)



/** TASK C **/
// to do



/** TASK D **/
// to do



/** TASK E **/
// to do



pred show {}
run show for exactly 4 ActorID, exactly 4 Actor,  6 MyString, exactly 4 Content




