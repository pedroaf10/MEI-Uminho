package com.gamehub.Repositories;

import com.gamehub.Model.Users.Utilizador;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

import java.math.BigInteger;
import java.util.List;


public interface UtilizadorRepository extends CrudRepository<Utilizador, Integer> {
    List<Utilizador> findByEmail(String email);

    String existeUsername = "SELECT EXISTS (SELECT nome FROM gamer WHERE nome=:nome)";

    String existeEmail = "SELECT EXISTS (SELECT email FROM utilizador WHERE email=:email)";

    String deleteUtilizadorGamer = "delete from utilizador where gamer_id = :id";

    @Modifying
    @Query(value = deleteUtilizadorGamer, nativeQuery = true)
    @Transactional
    void deleteUtilizadorGamer(@Param("id") int id);

    @Query(value = existeUsername, nativeQuery = true)
    BigInteger existeUsername(@Param("nome") String nome);

    @Query(value = existeEmail, nativeQuery = true)
    BigInteger existeEmail(@Param("email") String email);
}
