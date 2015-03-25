// check that git push works
// ************************************** SOCIAL NETWORK ******************************************* //

// social network is a set of interacting actors
// there is only one single social network
one sig SocialNetwork {
	actors: some Actor
}

// ************************************** ACTORS ******************************************* //

abstract some sig Actor {
	id: one ID,
	contents: set Content
}

some sig User extends Actor {
	friends: some User,
	follow: set Actor,
	block: set User,
	newsfeed: set Content
}

some sig Group extends Actor {
	members: some User,
	admins: some User
}

sig ID {
}

fact unique_id {
	// ids are unique
	all disjoint a1, a2: Actor | a1.id != a2.id
}

fact one_social_network {
	// all actors belong to the same social network
	all s: SocialNetwork | s.actors = Actor
}

fact friends {
	// friendships are mutual
	all u1, u2: User | u1 in u2.friends <=> u2 in u1.friends
}

fact not_in_own_lists {
	// actor doesn't follow or block itself, and is not his own friend
	all u: User | u not in u.friends and u not in u.follow and u not in u.block
}

fact admins_are_members {
	// every admin has to be a member of the group
	all g: Group | g.admins in g.members
}

fact group_members_not_follow {
	// a group member doesn't follow the group
	all g: Group, m: g.members | g not in m.follow
}

// ************************************** CONTENT ******************************************* //

abstract some sig Content {
	sender: one Actor,
	privacy: one Privacy,
	viewers: set User,
	modifiers: set User
}

abstract sig NonCommentable extends Content {}

// groups also have PersonalData (e.g. group name)
sig PersonalData extends NonCommentable {
	type: String, // e.g. "Name"
	data: String // e.g. "Rik"
}

sig Message extends NonCommentable {
	text: String,
	photos: set Photo,
	receiver: one User
}

abstract sig Commentable extends Content {
	comments: set Comment
}

sig Post extends Commentable {
	text: String,
	photos: set Photo
}

sig Photo extends Commentable {}

sig Comment extends Commentable {
	text: String,
	comment_on: Commentable
}

fact receiver_sender {
	// don't send a message to yourself
	all m: Message | m.sender != m.receiver
}

fact no_comment_itself {
	// no recursive comments
	all c: Comment | c != c.comment_on
}

// ************************************** PRIVACY ******************************************* //

// Pri = Private; Fri = Friends; FoF = Friends of Friends; Tra = Transitive Friends; Pub = Public
enum Privacy { Pri, Fri, FoF, Tra, Pub }
// this is the same as:
// abstract sig Privacy {}
// one sig Private, Friends, FriendsOfFriends, TransitiveFriends, Public

fact viewers {
	// privacy rules for content sent by users
	all c: Content, s: (c.sender & User) {c.viewers =
		{ u:s | c.privacy in Pri} 
		+ { u: s.friends | c.privacy in Fri} 
		+ { u: s.friends.friends | c.privacy in FoF}
		+ { u: s.*friends | c.privacy in Tra}
		+ { u: User | c.privacy in Pub}
		- s.block
		+ {m: c.receiver | c in Message}
	}
	// privacy rules for content sent by groups
	all c: Content, s: (c.sender & Group) {c.viewers = 
		{ u: User | c.privacy in Pub}
		+ { u: s.members |  c.privacy not in Pub}
	}
}

// ************************************** GENERAL FACTS ******************************************* //

fact newsfeed {
	// a content comes a a users newsfeed if the user is allowed to see it and
	// if the user follows the sender
	all u: User, c: Content | u in c.viewers and c.sender in u.follow <=> c in u.newsfeed
}

fact sender {
	// a content appears in the contents list of the sender
	all c: Content | c in c.sender.contents
}

fact unique_sender {
	// a message can only be sent by one actor
	all c: Content, disjoint a1, a2: Actor | not (c in a1.contents and c in a2.contents)
}

fact modifiers {
	// in case the sender of a content is a user, the modifier is the sender
	all c: Content, s: (c.sender & User) | c.modifiers = s
	// in case the sender iof a content is a group, the modifiers are the administrators
	all c: Content, s: (c.sender & Group) | c.modifiers = s.admins
}

pred show {}

run show
