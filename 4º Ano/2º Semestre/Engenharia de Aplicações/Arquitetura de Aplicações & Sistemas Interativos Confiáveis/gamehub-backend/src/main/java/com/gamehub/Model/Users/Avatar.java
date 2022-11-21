package com.gamehub.Model.Users;

import com.fasterxml.jackson.annotation.JsonProperty;

import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;

@Entity
public class Avatar {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private String link;

    public Avatar(int id,
                  String link) {
        this.id = id;
        this.link = link;
    }

    public Avatar(
            @JsonProperty("link") String link) {
        this.link = link;
    }


    public Avatar() {

    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getLink() {
        return link;
    }

    public void setLink(String link) {
        this.link = link;
    }


    @Override
    public String toString() {
        return "Avatar{" +
                "id=" + id +
                ", link='" + link + '\'' +
                '}';
    }
}
