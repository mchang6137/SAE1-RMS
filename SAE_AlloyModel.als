abstract sig Actor{
	allowedFollowers:set userID,
	blockedFollowers: set userID,
}

//User Defined traits

sig user extends Actor
{
	id: one userID,
	//Friends should be a mutual agreement
	friends: set userID
}

//************************************************************************************************
//Establish content on the basis of commentability

abstract sig Content{
	privacySetting:Privacy,
	creator: userID
}

abstract sig Commentable extends Content
{
	allcomments: set comment
}

sig Post extends Commentable
{
	text:String, 
	photoLink: set String, 
}

sig Picture extends Commentable
{
	text:String
}

sig comment
{
	commentString: String
}

abstract sig NonCommentable extends Content{}

sig personalData extends NonCommentable
{
	detail:String
}

sig messages extends NonCommentable
{
	messageText: String,
	photoLink: set String,
	//Remove sender? Is it necessary?
	sender:userID,
	receiver:userID
}

//************************************************************************************************
//Establish Privacy Settings
abstract sig Privacy{}

sig groupLevel extends Privacy{
	myGroupCircle:group_circleTypes
}

abstract sig personalLevel extends Privacy{}

enum personal_circleTypes{Private, Friends, FriendsOfFriends, TransitiveFriends, personal_Public}
enum group_circleTypes{group_Public, Group}

sig oneToOne extends personalLevel
{}

sig Circle extends personalLevel
{
	myCircle: personal_circleTypes
}

//************************************************************************************************

sig group extends Actor
{
	adminstrators: set userID,
	groupMembers:set userID
}

//***********************************************************************************************
//Listing the constraints of the network

fact check_uniqueID
{
	all disjoint u, u':user | u.id != u'.id
}

fact idSameUniverse
{
	all u: u' | u.id in u.allowedFollowers
}


//***********************************************************************************************
sig userID
{}

pred show{
}
run show 
